#include "solver.h"
#include "util.h"
#include "sim.h"
#include "sld.h"

#include <iterator>
#include <algorithm>
#include <boost/lexical_cast.hpp>
#include <random>

#ifdef CPLEX_ENABLED
#include <ilcplex/ilocplex.h>
ILOSTLBEGIN
#endif

solver_t::solver_t(ckt_n::ckt_t& c, ckt_n::ckt_t& s, int verb)
    : ckt(c)
    , simckt(s)
    , sim(s, s.ckt_inputs)
    , dbl(c, ckt_n::dup_allkeys, true)
    , cex_assumptions(c.num_key_inputs() + 1)
    , cand_assumptions(c.num_ckt_inputs())
    , input_values(ckt.num_ckt_inputs(), false)
    , output_values(ckt.num_outputs(), false)
    , fixed_keys(ckt.num_key_inputs(), false)
    , appsat_sim(c)
    , key_values(keyinput_literals_A.size(), false)
    , appsat_outputs(ckt.num_outputs(), false)
    , bit_generator(0, 1)
    , appsat_settlement_count(0)
    , verbose(verb)
    , iter(0)
    , backbones_count(0)
    , cube_count(0)
{
    MAX_VERIF_ITER = appsat_iter ? 10*appsat_queries : 1;
    time_limit = 1e100;

    using namespace ckt_n;
    using namespace sat_n;
    using namespace AllSAT;

    assert(dbl.dbl->num_outputs() == 1);
    assert(dbl.ckt.num_ckt_inputs() == ckt.num_ckt_inputs());

    // set up the Scex solver.
    dbl.dbl->init_solver(Scex, cl, lmap, true);
    node_t* out = dbl.dbl->outputs[0];
    l_out = lmap[out->get_index()];
    cl.verbose = verbose;

    // setup arrays of literals.
    for(unsigned i=0; i != ckt.num_key_inputs(); i++) {
        int idx = ckt.key_inputs[i]->get_index();
        keyinput_literals_A.push_back(lmap[dbl.pair_map[idx].first->get_index()]);
        keyinput_literals_B.push_back(lmap[dbl.pair_map[idx].second->get_index()]);
    }
    for(unsigned i=0; i != ckt.num_ckt_inputs(); i++) {
        int idx = ckt.ckt_inputs[i]->get_index();
        cktinput_literals.push_back(lmap[dbl.pair_map[idx].first->get_index()]);
    }
    for(unsigned i=0; i != ckt.num_outputs(); i++) {
        int idx = ckt.outputs[i]->get_index();
        node_t* outA = dbl.pair_map[idx].first;
        node_t* outB = dbl.pair_map[idx].second;
        Lit lA = lmap[outA->get_index()];
        Lit lB = lmap[outB->get_index()];
        output_literals_A.push_back(lA);
        output_literals_B.push_back(lB);
    }

    Scex.freeze(keyinput_literals_A);
    Scex.freeze(keyinput_literals_B);
    Scex.freeze(cktinput_literals);
    Scex.freeze(output_literals_A);
    Scex.freeze(output_literals_B);
    Scex.freeze(l_out);

    Scex_nProblemVars = Scex.nVars();
    dbl_keyinput_flags.resize(Scex_nProblemVars, false);
    dbl.dbl->init_keyinput_map(lmap, dbl_keyinput_flags);


    // now setup the candidate solver
    ckt.init_solver(Scand, candidate_cl, candidate_lmap, true);
    candidate_cl.verbose = verbose;

    // setup arrays.
    for (unsigned i=0; i != ckt.num_key_inputs(); i++) {
        int idx = ckt.key_inputs[i]->get_index();
        candidate_keyinput_literals.push_back(candidate_lmap[idx]);
        candidate_keyinputs.push_back(candidate_lmap[idx].toCNFInt());
    }
    for (unsigned i=0; i != ckt.num_ckt_inputs(); i++) {
        int idx = ckt.ckt_inputs[i]->get_index();
        candidate_cktinput_literals.push_back(candidate_lmap[idx]);
    }
    for (unsigned i=0; i != ckt.num_outputs(); i++) {
        int idx = ckt.outputs[i]->get_index();
        candidate_output_literals.push_back(candidate_lmap[idx]);
    }
    Scand.freeze(candidate_keyinput_literals);
    Scand.freeze(candidate_cktinput_literals);
    Scand.freeze(candidate_output_literals);
    Scand_nProblemVars = Scand.nVars();
    ckt_keyinput_flags.resize(Scand_nProblemVars, false);
    ckt.init_keyinput_map(candidate_lmap, ckt_keyinput_flags);

    // Create the map from the candidate solver's literals to the cex solver's.
    for (unsigned i=0; i != ckt.num_nodes(); i++) {
        int idx = ckt.nodes[i]->get_index();
        Lit cand_lit = candidate_lmap[idx];
        Lit cex_lit = lmap[dbl.pair_map[idx].second->get_index()];
        Scand_to_Scex_map[cand_lit] = cex_lit;
        Scand_to_Scex_map[~cand_lit] = ~cex_lit;
    }
}

void solver_t::addKnownKeys(std::vector<std::pair<int, int> >& values)
{
    for(unsigned i=0; i != values.size(); i++) {
        using namespace sat_n;
        Lit lA = keyinput_literals_A[values[i].first];
        Lit lB = keyinput_literals_B[values[i].first];
        assert(values[i].second == 0 || values[i].second == 1);
        if(values[i].second) {
            Scex.addClause(lA);
            Scex.addClause(lB);
        } else {
            Scex.addClause(~lA);
            Scex.addClause(~lB);
        }
    }
}

solver_t::~solver_t()
{
}

bool solver_t::solve(solver_t::solver_version_t ver, rmap_t& keysFound, bool quiet)
{
    assert( SOLVER_V0 == ver );
    return _solve_v0(keysFound, quiet, -1);
}

void solver_t::_record_sim(
    const std::vector<bool>& input_values, 
    const std::vector<bool>& output_values, 
    std::vector<sat_n::lbool>& values,
    std::vector<sat_n::lbool>& candidate_values
)
{
    using namespace sat_n;
    using namespace ckt_n;
    using namespace AllSAT;

    iovectors.push_back(iovalue_t());
    int last = iovectors.size()-1;
    iovectors[last].inputs = input_values;
    iovectors[last].outputs = output_values;

    // extract inputs and put them in the array.
    std::cout << "DIP=<";
    for(unsigned i=0; i != input_values.size(); i++) {
        lbool val = input_values[i] ? l_True : l_False;
        int jdx  = dbl.dbl->ckt_inputs[i]->get_index();
        assert(var(lmap[jdx]) < values.size());
        assert(var(lmap[jdx]) >= 0);
        values[var(lmap[jdx])] = val;
        std::cout << input_values[i];

        int idx = ckt.ckt_inputs[i]->get_index();
        candidate_values[var(candidate_lmap[idx])] = val;
    }
    std::cout << "> ";

    std::cout << "O(DIP)=<";
    // and then the outputs.
    for(unsigned i=0; i != ckt.num_outputs(); i++) {
        node_t* n_i = ckt.outputs[i];
        int idx = n_i->get_index();
        int idxA = dbl.pair_map[idx].first->get_index();
        int idxB = dbl.pair_map[idx].second->get_index();
        Var vA = var(lmap[idxA]);
        Var vB = var(lmap[idxB]);
        Var v = var(candidate_lmap[idx]);
        assert(vA < values.size() && vA >= 0);
        assert(vB < values.size() && vB >= 0);
        if(output_values[i] == true) {
            candidate_values[v] = values[vA] = values[vB] = sat_n::l_True;
            std::cout << "1";
        } else {
            candidate_values[v] = values[vA] = values[vB] = sat_n::l_False;
            std::cout << "0";
        }
    }
    std::cout << ">\n";
}

// Evaluates the output for the values stored in input_values and then records
// this in the solver.
void solver_t::_record_input_values()
{
    std::vector<sat_n::lbool> values(Scex_nProblemVars, sat_n::l_Undef);
    std::vector<sat_n::lbool> candidate_values(Scand_nProblemVars, sat_n::l_Undef);

    sim.eval(input_values, output_values);
    _record_sim(input_values, output_values, values, candidate_values);

    int cnt = candidate_cl.addRewrittenClauses(values, dbl_keyinput_flags, Scand_to_Scex_map, Scex);
    __sync_fetch_and_add(&cube_count, cnt);

    cnt = candidate_cl.addRewrittenClauses(candidate_values, ckt_keyinput_flags, Scand);
    __sync_fetch_and_add(&cube_count, cnt);

    _dump_io_vectors();
}

void solver_t::_dump_io_vectors()
{
    using namespace ckt_n;

    if(verbose) {
        std::cout << "input: " << input_values
                  << "; output: " << output_values << std::endl;
    }
}

// Try to get a distinguishing input. Returns false if none exists (that is,
// we are done).
bool solver_t::_get_distinguishing_input()
{
    using namespace sat_n;
    using namespace ckt_n;
    bool cand_result = Scand.solve();
    assert (cand_result == true);
    cex_assumptions[0] = l_out;
    for (unsigned i=0; i != ckt.num_key_inputs(); i++) {
        lbool lki = Scand.modelValue(candidate_keyinput_literals[i]);
        assert (lki.isDef());
        if (lki.getBool()) {
            cex_assumptions[i+1] = keyinput_literals_A[i];
        } else {
            cex_assumptions[i+1] = ~keyinput_literals_A[i];
        }
    }

    bool result = Scex.solve(cex_assumptions);
    __sync_fetch_and_add(&iter, 1);
    // TODO [pramod]: who is even setting these options anymore?
    if (cnf_dump_prefix.size()) {
        std::string filename = cnf_dump_prefix + "_" + 
                               boost::lexical_cast<std::string>(iter) + ".cnf";
        Scand.writeCNF_WithAnnotation(filename, "ind", candidate_keyinputs.data(), candidate_keyinputs.size(), 8);
    }
    if(false == result) {
        return false;
    }

    // now extract the inputs.
    // std::cout << "DIP=<";
    for(unsigned i=0; i != dbl.dbl->num_ckt_inputs(); i++) {
        int jdx  = dbl.dbl->ckt_inputs[i]->get_index();
        lbool val = Scex.modelValue(lmap[jdx]);
        assert(val.isDef());
        if(!val.getBool()) {
            input_values[i] = false;
            // std::cout << "0";
        } else {
            input_values[i] = true;
            // std::cout << "1";
        }
    }
    // std::cout << ">";
    return true;
}

bool solver_t::_solve_v0(rmap_t& keysFound, bool quiet, int dlimFactor)
{
    using namespace sat_n;
    using namespace ckt_n;
    using namespace AllSAT;

    int appsat_counter = 0;

    // FIXME: add a set of random vectors here.
    if (preload_vectors) {
        // add all zeros.
        std::fill(input_values.begin(), input_values.end(), false);
        _record_input_values();

        // and all ones.
        std::fill(input_values.begin(), input_values.end(), true);
        _record_input_values();
    }

    bool done = false;
    while(true) {
        bool di_exists = _get_distinguishing_input();
        if (!di_exists) {
            done = true;
            break;
        }
        // TODO [pramod]: who is even looking at this stuff anymore?
        if(dlimFactor != -1) {
            int dlim = dlimFactor * Scex.nVars();
            if(dlim <= Scex.getNumDecisions()) {
                std::cout << "too many decisions! giving up." << std::endl;
                break;
            }
        }
        std::cout << "iteration: " << iter 
                  << "; vars: " << Scex.nVars() 
                  << "; clauses: " << Scex.nClauses() 
                  << "; decisions: " << Scex.getNumDecisions() << std::endl;


        // now extract the inputs.
        _record_input_values();

        // _sanity_check_model();
        appsat_counter += 1;
        if (appsat_counter == appsat_iter) {
            appsat_counter = 0;
            int fail_count = _appsat_iteration();
            if (fail_count == 0) {
                appsat_settlement_count += 1;
            } else {
                appsat_settlement_count = 0;
            }
            std::cout << "appsat iteration: fail_count: " << fail_count
                      << "; settlement count: " << appsat_settlement_count
                      << std::endl;
            if (appsat_settlement_count >= appsat_threshold) {
                std::cout << "appsat settlement threshold reached. terminating." 
                          << std::endl;
                done = true;
                break;
            }
        }

        struct rusage ru_current;
        getrusage(RUSAGE_SELF, &ru_current);
        if(utimediff(&ru_current, &ru_start) > time_limit) {
            std::cout << "timeout in the slice loop." << std::endl;
            break;
        }
    }
    if(done) {
        int fail_count = _verify_solution_sim(keysFound);
        std::cout << "finished solver loop. fail_count = " 
                  << fail_count << std::endl;
    }
    return done;
}

int solver_t::_appsat_iteration()
{
    int fail_count = 0;
    for (int i = 0; i < appsat_queries; i++) {
        if(!_appsat_random_query()) {
            fail_count += 1;
        }
    }
    return fail_count;
}

bool solver_t::_appsat_random_query()
{
    using namespace sat_n;
    using namespace ckt_n;

    // create a random input.
    for (unsigned i=0; i != input_values.size(); i++) {
        bool vi = static_cast<bool>(bit_generator(mersenne_twister));
        cand_assumptions[i] = vi 
                ? candidate_cktinput_literals[i] 
                : ~candidate_cktinput_literals[i];
        input_values[i] = vi;
    }
    sim.eval(input_values, output_values);
    if(verbose) {
        std::cout << "[appsat] input: " << input_values 
                  << "; output: " << output_values << std::endl;
    }

    // check with current SAT solver state.
    bool sat = Scand.solve(cand_assumptions);
    assert (sat); // must be SATisfiable.

    // now compare with simulation output.
    bool pass = true;
    if (verbose) {
        std::cout << "[appsat] ckt_output: ";
    }
    for(unsigned i=0; i != output_values.size(); i++) {
        bool vi = output_values[i];
        lbool ri = Scand.modelValue(candidate_output_literals[i]);
        if (verbose) {
            if (!ri.isDef()) {
                std::cout << "-";
            } else {
                std::cout << static_cast<int>(ri.getBool());
            }
        }
        if(!(ri.isDef() && ri.getBool() == vi)) { 
            pass = false;
        }
    }
    if (verbose) {
        std::cout << std::endl;
    }

    // now add this I/O pattern to the solver.
    std::vector<sat_n::lbool> values(Scex_nProblemVars, sat_n::l_Undef);
    std::vector<sat_n::lbool> candidate_values(Scand_nProblemVars, sat_n::l_Undef);

    _record_sim(input_values, output_values, values, candidate_values);
    int cnt = candidate_cl.addRewrittenClauses(values, dbl_keyinput_flags, Scand_to_Scex_map, Scex);
    __sync_fetch_and_add(&cube_count, cnt);
    cnt = candidate_cl.addRewrittenClauses(candidate_values, ckt_keyinput_flags, Scand);
    __sync_fetch_and_add(&cube_count, cnt);

    // return pass/fail.
    return pass;
}

void solver_t::_sanity_check_model()
{
    using namespace sat_n;
    using namespace ckt_n;

    bool pass = true;
    vec_lit_t assumps;
    std::vector<bool> actual_output_values;

    for(unsigned i=0; i != cktinput_literals.size(); i++) {
        bool vi = input_values[i];
        assumps.push( vi ? cktinput_literals[i] : ~cktinput_literals[i]);
    }
    if(Scex.solve(assumps) == false) {
        std::cout << "UNSAT result during sanity check." << std::endl;
        std::cout << "result of no-assumption solve: " << Scex.solve() << std::endl;
        exit(1);
    }

    for(unsigned i=0; i != output_values.size(); i++) {
        bool vi = output_values[i];
        lbool ri = Scex.modelValue(output_literals_A[i]);
        if(!(ri.isDef() && ri.getBool() == vi)) { 
            pass = false;
        }
    }

    if(pass) {
        if(verbose) {
            std::cout << "simulation sanity check passed." << std::endl;
        }
    } else {
        std::cout << "simulation sanity check failed." << std::endl;
        exit(1);
    }
}

void solver_t::blockKey(rmap_t& keysFound)
{
    using namespace sat_n;

    vec_lit_t bc(candidate_keyinput_literals.size());
    for(unsigned i=0; i != keyinput_literals_A.size(); i++) {
        auto &&name_i = ckt.key_inputs[i]->name;
        assert (keysFound.find(name_i)  != keysFound.end());
        auto ki = keysFound[ckt.key_inputs[i]->name];
        bc[i] = ki ? ~candidate_keyinput_literals[i] : candidate_keyinput_literals[i];
    }
    Scand.addClause(bc);
}

bool solver_t::getNewKey(rmap_t& keysFound)
{
    keysFound.clear();
    return _verify_solution_sim(keysFound) == 0;
}

int solver_t::_verify_solution_sim(rmap_t& keysFound)
{
    using namespace sat_n;
    using namespace ckt_n;

    int fail_count = 0;
    for(int iter=0; iter < MAX_VERIF_ITER;  iter++) {
        vec_lit_t assumps;
        std::vector<bool> input_values;
        std::vector<bool> output_values;

        for(unsigned i=0; i != candidate_cktinput_literals.size(); i++) {
            bool vi = static_cast<bool>(bit_generator(mersenne_twister));
            assumps.push( vi ? candidate_cktinput_literals[i] : ~candidate_cktinput_literals[i]);
            input_values.push_back(vi);
        }
        sim.eval(input_values, output_values);
        if(verbose) {
            std::cout << "input: " << input_values 
                      << "; output: " << output_values << std::endl;
            dump_clause(std::cout << "assumps: ", assumps) << std::endl;
        }

        if(Scand.solve(assumps) == false) {
            std::cout << "UNSAT model!" << std::endl;
            return -1;
        }

        if(verbose) {
            dump_clause(std::cout << "sat input: ", assumps) << std::endl;
            std::cout << "sat output: ";
        }
        for(unsigned i=0; i != output_values.size(); i++) {
            bool vi = output_values[i];
            lbool ri = Scand.modelValue(candidate_output_literals[i]);
            if(verbose) {
                std::cout << (ri.isUndef() ? "-" : (ri.getBool() ? "1" : "0"));
            }
            if(!(ri.isDef() && ri.getBool() == vi)) { 
                fail_count += 1;
                break;
            }
        }
        if(iter == 0) {
            _extractSolution(keysFound);
        }
        if(verbose) std::cout << std::endl;
    }
    return fail_count;
}

void solver_t::_extractSolution(rmap_t& keysFound)
{
    using namespace sat_n;

    for(unsigned i=0; i != keyinput_literals_A.size(); i++) {
        lbool v = Scand.modelValue(candidate_keyinput_literals[i]);
        if(!v.getBool()) {
            keysFound[ckt.key_inputs[i]->name] = 0;
        } else {
            keysFound[ckt.key_inputs[i]->name] = 1;
        }
    }
}

int solver_t::sliceAndSolve( rmap_t& keysFoundMap, int maxKeys, int maxNodes )
{
#ifdef CPLEX_ENABLED
    using namespace ckt_n;
    using namespace sat_n;

    if(maxNodes != -1) {
        assert(maxNodes <= (int) ckt.nodes.size());
        assert(maxNodes > 0);
    }
    if(maxKeys != -1) {
        assert(maxKeys <= (int) ckt.num_key_inputs());
        assert(maxKeys > 0);
    }

    // initialize the maps.
    assert(ckt.gates.size() == ckt.gates_sorted.size());
    assert(ckt.nodes.size() == ckt.nodes_sorted.size());

    std::vector< std::vector<bool> > keymap, outputmap;
    ckt.init_keymap(keymap);
    ckt.init_outputmap(outputmap);

    IloEnv env;

    int numNodeVars = ckt.num_nodes();
    int numOutputVars = ckt.num_outputs();
    int numKeyVars = ckt.num_key_inputs();
    int totalVars = numNodeVars + numOutputVars + numKeyVars;

    auto outVarIndex = [numNodeVars](int i) -> int 
        { return numNodeVars + i; };
    auto keyVarIndex = [numNodeVars, numOutputVars](int i) -> int 
        { return numNodeVars + numOutputVars + i; };


    // first create the variables.
    IloNumVarArray vars(env);
    int i;
    for(i=0; i != numNodeVars; i++) {
        char name[64];
        sprintf(name, "n_%s_%d", ckt.nodes[i]->name.c_str(), i);
        vars.add(IloNumVar(env, 0, 1, ILOINT, name));
    }
    for(; i < numNodeVars+numOutputVars; i++) {
        char name[64];
        sprintf(name, "o_%s_%d", ckt.outputs[i-numNodeVars]->name.c_str(), i);
        vars.add(IloNumVar(env, 0, 1, ILOINT, name));
        assert(outVarIndex(i-numNodeVars) == i);
    }
    for(; i < numNodeVars+numOutputVars+numKeyVars; i++) {
        char name[64];
        sprintf(name, "k_%s_%d", ckt.key_inputs[i-numNodeVars-numOutputVars]->name.c_str(), i);
        vars.add(IloNumVar(env, 0, 1, ILOINT, name));
        assert(keyVarIndex(i-numNodeVars-numOutputVars) == i);
    }
    assert(i == totalVars);

    // and then the constraints.
    IloRangeArray cnst(env);
    int ccPos=0; // current constraint position.

    // for each key ki: ki => oj for each ouput j that is affected bby ki
    // ki => oj translates to -ki + oj >= 0
    for(unsigned i=0; i != ckt.num_key_inputs(); i++) {
        std::vector<int> output_indices;
        ckt.get_indices_in_bitmap(outputmap, ckt.key_inputs[i], output_indices);
        for(auto it = output_indices.begin(); it != output_indices.end(); it++) {
            unsigned j=*it;
            int vi = keyVarIndex(i);
            int vj = outVarIndex(j);
            char name[16]; sprintf(name, "c%d", ccPos);
            cnst.add(IloRange(env, 0, IloInfinity, name));
            cnst[ccPos].setLinearCoef(vars[vi], -1);
            cnst[ccPos].setLinearCoef(vars[vj], 1);
            ccPos += 1;
        }
    }

    // for each output oi, and each node nj in the fanin cone of that output:
    // oi => nj <=> -oi + nj >= 0
    ckt.check_sanity();
    for(unsigned i=0; i != ckt.num_outputs(); i++) {
        std::vector<bool> fanin(ckt.num_nodes());
        ckt.compute_transitive_fanin(ckt.outputs[i], fanin);

        for(int j=0; j != (int)fanin.size(); j++) {
            if(fanin[j]) {
                node_t* nj = ckt.nodes[j];
                assert(nj->get_index() == j);
                int vi = outVarIndex(i);
                int vj = j;
                char name[16]; sprintf(name, "c%d", ccPos);
                cnst.add(IloRange(env, 0, IloInfinity, name));
                cnst[ccPos].setLinearCoef(vars[vi], -1);
                cnst[ccPos].setLinearCoef(vars[vj], 1);
                ccPos += 1;
            }
        }
    }

    // now create the objective function
    IloObjective obj;
    IloNumArray coeffs(env, totalVars);
    if(maxKeys == -1) {
        // maximize the number of selected keys.
        obj = IloMaximize(env);
        for(int i=0; i != numKeyVars; i++) {
            coeffs[keyVarIndex(i)] = 1;
        }
    } else {
        // minimize: number of selected nodes.
        obj = IloMinimize(env);
        for(int i=0; i != numNodeVars; i++) {
            coeffs[i] = 1;
        }
    }
    obj.setLinearCoefs(vars, coeffs);

    if(maxNodes != -1) {
        // n1 + n2 + ... + nk <= maxNodes
        char name[16]; sprintf(name, "c%d", ccPos);
        cnst.add(IloRange(env, 0, maxNodes, name));
        int nodeCnstPos = ccPos++;
        for(int i=0; i != numNodeVars; i++) {
            cnst[nodeCnstPos].setLinearCoef(vars[i], 1);
        }
    }
    if(maxKeys != -1) {
        // k1 + k2 + ... + kl >= maxKeys
        char name[16]; sprintf(name, "c%d", ccPos);
        cnst.add(IloRange(env, maxKeys, IloInfinity, name));
        int keyCnstPos = ccPos++;
        for(int i=0; i != numKeyVars; i++) {
            int ki = keyVarIndex(i);
            cnst[keyCnstPos].setLinearCoef(vars[ki], 1);
        }
    } else {
        // k1 + k2 + ... + kl >= 1
        char name[16]; sprintf(name, "c%d", ccPos);
        cnst.add(IloRange(env, 1, IloInfinity, name));
        int keyCnstPos = ccPos++;
        for(int i=0; i != numKeyVars; i++) {
            int ki = keyVarIndex(i);
            cnst[keyCnstPos].setLinearCoef(vars[ki], 1);
        }
    }

    IloModel model(env);
    model.add(obj);
    model.add(cnst);
    IloCplex cplex(model);
    cplex.setOut(env.getNullStream());
    cplex.setParam(IloCplex::TiLim, 1);
    cplex.setParam(IloCplex::EpGap, 0.25);

    static int cnt=0;
    char buf[24]; sprintf(buf, "model%d.lp", cnt++);
    cplex.exportModel(buf);

    if(!cplex.solve()) {
        return 0;
    }

    IloNumArray vals(env);
    cplex.getValues(vals, vars);

    slice_t slice(ckt, simckt);
    for(int i=0; i != numOutputVars; i++) {
        int index = outVarIndex(i);
        int vi = (int) vals[index];
        if(vi) {
            slice.outputs.push_back(i);
        }
    }

    //std::cout << "selected keys: ";
    for(int i =0; i != numKeyVars; i++) {
        int index = keyVarIndex(i);
        int vi = (int) vals[index];
        if(vi) {
            slice.keys.push_back(i);
            //std::cout << i << "/" << index << " ";
        }
    }

    assert(maxNodes < (int) ckt.num_nodes() || slice.keys.size() == ckt.num_key_inputs());
    //std::cout << std::endl;

    std::cout << "# of outputs: " << slice.outputs.size() << std::endl;
    std::cout << "# of keys: " << slice.keys.size() << std::endl;
    std::cout << "objective : " << cplex.getObjValue() << std::endl;

    std::map<int, int> keysFound;
    rmap_t allKeys;
    this->solveSlice(slice, keysFound, allKeys);
    for(auto it = keysFound.begin(); it != keysFound.end(); it++) {
        int keyIndex = it->first;
        int keyValue = it->second;
        const std::string& keyName = ckt.key_inputs[keyIndex]->name;
        keysFoundMap[keyName] = keyValue;
    }
    if(ckt.num_key_inputs() == slice.cktslice->num_key_inputs()) {
        for(auto it = allKeys.begin(); it != allKeys.end(); it++) {
            int keyValue = it->second;
            const std::string& keyName = it->first;
            keysFoundMap[keyName] = keyValue;
        }
    }

    std::vector<lbool> keyValues(ckt.num_key_inputs(), sat_n::l_Undef);
    for(unsigned ki=0; ki != ckt.num_key_inputs(); ki++) {
        auto pos = keysFound.find(ki);
        if(pos != keysFound.end()) {
            keyValues[ki] = (pos->second ? sat_n::l_True : sat_n::l_False);
        }
        else if(allKeys.size() != 0 && ckt.num_key_inputs() == slice.cktslice->num_key_inputs()) {
            auto mapPos = allKeys.find(ckt.key_inputs[ki]->name);
            assert(mapPos != allKeys.end());
            keyValues[ki] = (mapPos->second ? sat_n::l_True : sat_n::l_False);
        }
    }
    ckt.rewrite_keys(keyValues);
    return slice.outputs.size();
#else
    std::cerr << "Error: can't slice and solve because sld was not compiled with CPLEX." << std::endl;
    exit(1);
    return -1;
#endif
}

void solver_t::sliceAndDice(
    ckt_n::ckt_t& ckt, 
    ckt_n::ckt_t& sim, 
    std::vector<slice_t*>& slices
)
{
#ifdef CPLEX_ENABLED
    using namespace ckt_n;

    // initialize the maps.
    std::vector< std::vector<bool> > keymap, outputmap;
    ckt.init_keymap(keymap);
    ckt.init_outputmap(outputmap);

    IloEnv env;

    int numNodeVars = ckt.num_nodes();
    int numOutputVars = ckt.num_outputs();
    int numKeyVars = ckt.num_key_inputs();
    int totalVars = numNodeVars + numOutputVars + numKeyVars;

    // std::cout << "# of outputs: " << numOutputVars << std::endl;
    // std::cout << "# of nodes: " << numNodeVars << std::endl;
    // std::cout << "# of keys: " << numKeyVars << std::endl;

    auto outVarIndex = [numNodeVars](int i) -> int 
        { return numNodeVars + i; };
    auto keyVarIndex = [numNodeVars, numOutputVars](int i) -> int 
        { return numNodeVars + numOutputVars + i; };


    // first create the variables.
    IloNumVarArray vars(env);
    int i;
    for(i=0; i != numNodeVars; i++) {
        char name[32];
        sprintf(name, "n%d", i);
        vars.add(IloNumVar(env, 0, 1, ILOINT, name));
    }
    for(; i < numNodeVars+numOutputVars; i++) {
        char name[32];
        sprintf(name, "o%d", i);
        vars.add(IloNumVar(env, 0, 1, ILOINT, name));
        assert(outVarIndex(i-numNodeVars) == i);
    }
    for(; i < numNodeVars+numOutputVars+numKeyVars; i++) {
        char name[32];
        sprintf(name, "k%d", i);
        vars.add(IloNumVar(env, 0, 1, ILOINT, name));
        assert(keyVarIndex(i-numNodeVars-numOutputVars) == i);
    }
    assert(i == totalVars);

    // and then the constraints.
    IloRangeArray cnst(env);
    int ccPos=0; // current constraint position.

    // for each key ki: ki => oj for each ouput j that is affected bby ki
    // ki => oj translates to -ki + oj >= 0
    for(unsigned i=0; i != ckt.num_key_inputs(); i++) {
        std::vector<int> output_indices;
        ckt.get_indices_in_bitmap(outputmap, ckt.key_inputs[i], output_indices);
        for(auto it = output_indices.begin(); it != output_indices.end(); it++) {
            unsigned j=*it;
            int vi = keyVarIndex(i);
            int vj = outVarIndex(j);
            cnst.add(IloRange(env, 0, IloInfinity));
            cnst[ccPos].setLinearCoef(vars[vi], -1);
            cnst[ccPos].setLinearCoef(vars[vj], 1);
            ccPos += 1;
        }
    }
    // for each output oi, and each node nj in the fanin cone of that output:
    // oi => nj <=> -oi + nj >= 0
    for(unsigned i=0; i != ckt.num_outputs(); i++) {
        std::vector<bool> fanin(ckt.num_nodes());
        ckt.compute_transitive_fanin(ckt.outputs[i], fanin);

        for(int j=0; j != (int)fanin.size(); j++) {
            if(fanin[j]) {
                node_t* nj = ckt.nodes[j];
                assert(nj->get_index() == j);
                int vi = outVarIndex(i);
                int vj = j;
                cnst.add(IloRange(env, 0, IloInfinity));
                cnst[ccPos].setLinearCoef(vars[vi], -1);
                cnst[ccPos].setLinearCoef(vars[vj], 1);
                ccPos += 1;
            }
        }
    }
    // now we need to create the objective function
    // minimize: number of selected nodes.
    IloObjective obj = IloMinimize(env);
    IloNumArray coeffs(env, totalVars);
    for(int i=0; i != numNodeVars; i++) {
        coeffs[i] = 1;
    }
    obj.setLinearCoefs(vars, coeffs);

    std::set<int> notYetSelectedKeys;
    for(int i=0; i != numKeyVars; i++) {
        notYetSelectedKeys.insert(i);
    }

    cnst.add(IloRange(env, 1, IloInfinity));
    int keyCnstPos = ccPos++;
    // k1 + k2 + ... + kn >= 1
    while(notYetSelectedKeys.size() > 0) {
        for(int i=0; i != numKeyVars; i++) {
            if(notYetSelectedKeys.find(i) != notYetSelectedKeys.end()) {
                int varNum = keyVarIndex(i);
                cnst[keyCnstPos].setLinearCoef(vars[varNum], 1);
            } else {
                int varNum = keyVarIndex(i);
                cnst[keyCnstPos].setLinearCoef(vars[varNum], 0);
            }
        }

        IloModel model(env);
        model.add(obj);
        model.add(cnst);
        IloCplex cplex(model);
        cplex.setOut(env.getNullStream());
        // cplex.exportModel("model.lp");
        if(!cplex.solve()) {
            std::cerr << "Error: unable to solve cplex model." << std::endl;
            exit(1);
        }
        // std::cout << "status: " << cplex.getStatus() << std::endl;
        // std::cout << "objval: " << cplex.getObjValue() << std::endl;
        IloNumArray vals(env);
        cplex.getValues(vals, vars);

        slice_t *slice = new slice_t(ckt, sim);
        for(int i=0; i != numOutputVars; i++) {
            int index = outVarIndex(i);
            int vi = (int) vals[index];
            if(vi) {
                slice->outputs.push_back(i);
            }
        }
        for(int i =0; i != numKeyVars; i++) {
            int index = keyVarIndex(i);
            int vi = (int) vals[index];
            if(vi) {
                slice->keys.push_back(i);
                notYetSelectedKeys.erase(i);
            }
        }

        std::sort(slice->outputs.begin(), slice->outputs.end());
        std::sort(slice->keys.begin(), slice->keys.end());

        slices.push_back(slice);
    }
#else
    std::cerr << "Error: can't slice and solve because sld was not compiled with CPLEX." << std::endl;
    exit(1);
#endif
}

void solver_t::slice_t::createCkts()
{
    using namespace ckt_n;
    assert(sim.num_outputs() == ckt.num_outputs());

    // create output list.
    nodelist_t cktOutputs, simOutputs;
    for(unsigned i=0; i != outputs.size(); i++) {
        int index = outputs[i];
        assert(index >= 0 && index < (int) ckt.num_outputs());

        node_t* out_i = ckt.outputs[index];
        cktOutputs.push_back(out_i);

        node_t* out_j = sim.outputs[index];
        simOutputs.push_back(out_j);
    }

    // now construct slice.
    cktslice = new ckt_t(ckt, cktOutputs, ckt_nmfwd, ckt_nmrev);
    simslice = new ckt_t(sim, simOutputs, sim_nmfwd, sim_nmrev);
    // make sure the inputs and outputs match up.
    if(!cktslice->compareIOs(*simslice, 1)) {
        std::cerr << "CKT SLICE" << std::endl << cktslice << std::endl;
        std::cerr << "SIM SLICE" << std::endl << simslice << std::endl;
        std::cerr << "Error. Slices are not comparable." << std::endl;
        exit(1);
    }

    //std::cout << "# of nodes: " << ckt.nodes.size() << std::endl;
    //std::cout << "# of fwd mapped nodes: " << ckt_nmfwd.size() << std::endl;

    // create the maps between the key inputs in the original and new circuit.
    // key input map.
    for(unsigned i=0; i != ckt.num_key_inputs(); i++) {
        node_t* ki = ckt.key_inputs[i];
        auto pos = ckt_nmfwd.find(ki);
        if(pos != ckt_nmfwd.end()) {
            node_t* kj = pos->second;
            int index = cktslice->get_key_input_index(kj);
            assert(index != -1);
            cktm_kfwd[i] = index;
            cktm_krev[index] = i;
        }
    }

    // ckt input map.
    for(unsigned i=0; i != ckt.num_ckt_inputs(); i++) {
        node_t* ci = ckt.ckt_inputs[i];
        auto pos = ckt_nmfwd.find(ci);
        if(pos != ckt_nmfwd.end()) {
            node_t* cj = pos->second;
            int index = cktslice->get_ckt_input_index(cj);
            assert(index != -1);
            cktm_cfwd[i] = index;
            cktm_crev[index] = i;
        }
    }
}

void solver_t::solveSlice(
    slice_t& slice, 
    std::map<int, int>& fixedKeys, 
    rmap_t& allKeys 
)
{
    // first create the slice that is requested.
    using namespace ckt_n;

    assert(slice.sim.num_outputs() == slice.ckt.num_outputs());
    slice.createCkts();

    // make sure we don't have any known keys.
    // (the caller must've simplified them away).
    for(auto it=fixedKeys.begin();it != fixedKeys.end(); it++) {
        int i1 = it->first;
        int i2 = slice.mapKeyIndexFwd(i1);
        assert(i2 == -1);
    }

    // actual solving.
    solver_t S(*slice.cktslice, *slice.simslice, 0);
    S.MAX_VERIF_ITER = 1;

    S.time_limit = 60;
    getrusage(RUSAGE_SELF, &S.ru_start);
    bool finished = S.solve(solver_t::SOLVER_V0, allKeys, true);

    if(true||finished) {
        assert(slice.ckt.num_key_inputs() >= slice.cktslice->num_key_inputs());
        if(slice.ckt.num_outputs() > slice.cktslice->num_outputs()) {
            std::map<int, int> sliceKeys;
            S.findFixedKeys(sliceKeys);

            // now translate the keys back to big node.
            for(auto it=sliceKeys.begin(); it != sliceKeys.end(); it++) {
                int i1 = it->first;
                int i2 = slice.mapKeyIndexRev(i1);
                fixedKeys[i2] = it->second;
            }
        }
    }
}

void solver_t::findFixedKeys(std::map<int, int>& backbones)
{
    using namespace ckt_n;
    using namespace sat_n;

    if(iovectors.size() == 0) return;

    Solver Sckt;
    AllSAT::ClauseList cktCl;
    index2lit_map_t cktmap;
    std::vector<bool> keyinputflags;

    ckt.init_solver(Sckt, cktCl, cktmap, true /* don't care. */);
    keyinputflags.resize(Sckt.nVars(), false);
    ckt.init_keyinput_map(cktmap, keyinputflags);

    std::vector<lbool> values(Sckt.nVars(), sat_n::l_Undef);

    for(unsigned i=0; i != iovectors.size(); i++) {
        const std::vector<bool>& inputs = iovectors[i].inputs;
        const std::vector<bool>& outputs = iovectors[i].outputs;

        for(unsigned i=0; i != inputs.size(); i++) {
            int idx = ckt.ckt_inputs[i]->get_index();
            values[var(cktmap[idx])] = inputs[i] ? sat_n::l_True : sat_n::l_False;
        }

        for(unsigned i=0; i != outputs.size(); i++) {
            int idx = ckt.outputs[i]->get_index();
            values[var(cktmap[idx])] = outputs[i] ? sat_n::l_True : sat_n::l_False;
        }
        cktCl.addRewrittenClauses(values, keyinputflags, Sckt);
    }
    // now freeze the ckt inputs.
    for(unsigned i=0; i != ckt.num_ckt_inputs(); i++) {
        Lit li = cktmap[ckt.ckt_inputs[i]->get_index()];
        Sckt.freeze(li);
    }
    // and then freeze the key inputs.
    for(unsigned i=0; i != ckt.num_key_inputs(); i++) {
        Lit li = cktmap[ckt.key_inputs[i]->get_index()];
        Sckt.freeze(li);
    }

    // get an assignment for the keys.
    std::cout << "finding initial assignment of keys." << std::endl;
    bool result = Sckt.solve();
    assert(result);
    std::vector<Lit> keys;
    for(unsigned i=0; i != ckt.num_key_inputs(); i++) {
        int idx = ckt.key_inputs[i]->get_index();
        lbool value = Sckt.modelValue(var(lmap[idx]));
        keys.push_back(value == sat_n::l_True ? lmap[idx] : ~lmap[idx]);
    }
    for(unsigned i=0; i != ckt.num_key_inputs(); i++) {
        //std::cout << "key: " << i << std::endl;
        if(Sckt.solve(~keys[i]) == false) {
            // can't satisfy these I/O combinations with this key value.
            if(sign(keys[i])) {
                backbones[i] = 0;
            } else {
                backbones[i] = 1;
            }
            Sckt.addClause(keys[i]);
        }
    }

#if 0
    for(unsigned i=0; i != iovectors.size(); i++) {
        //std::cout << "iovector: " << i << std::endl;

        const std::vector<bool>& inputs = iovectors[i].inputs;
        _testBackbones(inputs, Sckt, cktmap, backbones);
    }
#endif
    //std::cout << "# of backbones found: " << backbones.size() << std::endl;
}
