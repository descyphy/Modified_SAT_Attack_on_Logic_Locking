#include "SATInterface.h"

namespace sat_n {
#ifndef CMSAT
    const lbool l_True(lbool::p_True);
    const lbool l_False(lbool::p_False);
    const lbool l_Undef(lbool::p_Undef);
    static void clause_count (void * voidptr, int lit) {
        unsigned int *cntptr = static_cast<unsigned int*>(voidptr);
        if (!lit) *cntptr += 1;
    }

    static void clause_print (void * voidptr, int lit) {
        FILE* out = static_cast<FILE*>(voidptr);
        if (lit) fprintf (out, "%d ", lit);
        else fprintf (out, "0\n");
    }

    static void dump_clauses(LGL* solver, FILE* fp, unsigned int init_count)
    {
        int count = init_count;
        lgltravall (solver, &count, clause_count);
        fprintf (fp, "p cnf %d %d\n", lglmaxvar (solver), count);
        lgltravall (solver, fp, clause_print);
    }

    void dump_clauses_w_annot(LGL* solver, FILE* fp, unsigned int init_count, 
                const char* prefix, int* lits, size_t nlits, int n_per_line)
    {
        int count = init_count;
        lgltravall (solver, &count, clause_count);
        fprintf (fp, "p cnf %d %d\n", lglmaxvar (solver), count);

        fprintf(fp, "c %s ", prefix);
        for(size_t lcnt = 0; lcnt < nlits; lcnt++) {
            fprintf(fp, " %d", lits[lcnt]);
            if (lcnt > 0 && (lcnt % n_per_line) == 0) {
                fprintf(fp, " 0\nc %s ", prefix);
            }
        }
        fprintf(fp, " 0\n");
        lgltravall (solver, fp, clause_print);
    }

    void Solver::writeCNF(const std::string& filename, const vec_lit_t& assumps) {
        FILE *fp = fopen(filename.c_str(), "wt");
        if (fp != NULL) {
            dump_clauses(solver, fp, assumps.size());
            for (unsigned i=0; i != assumps.size(); i++) {
                fprintf (fp, "%d 0\n", translate(assumps[i]));
            }
            fclose(fp);
        }
    }

    void Solver::writeCNF(const std::string& filename, Lit x) {
        FILE *fp = fopen(filename.c_str(), "wt");
        if (fp != NULL) {
            dump_clauses(solver, fp, 1);
            fprintf (fp, "%d 0\n", translate(x));
            fclose(fp);
        }
    }

    void Solver::writeCNF(const std::string& filename) {
        FILE* fp = fopen(filename.c_str(), "wt");
        if (fp != NULL) {
            dump_clauses(solver, fp, 1);
            fclose(fp);
        }
    }
    void Solver::writeCNF_WithAnnotation(const std::string& filename,
            const char* prefix, int *lits, size_t nlits, int n_per_line) {
        FILE* fp = fopen(filename.c_str(), "wt");
        if (fp != NULL) {
            dump_clauses_w_annot(solver, fp, 1, prefix, lits, nlits, n_per_line);
            fclose(fp);
        }
    }

#endif

}
