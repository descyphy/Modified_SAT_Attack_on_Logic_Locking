#include "sle.h"
#include "sld.h"
#include "encoder.h"
#include "mutability.h"
#include "dac12enc.h"
#include "randomins.h"
#include "optenc.h"
#include "toc13enc.h"
#include <math.h>

#include <iostream>
#include <fstream>
#include <unistd.h>
#include <stdio.h>
#include <signal.h>
#include <sys/time.h>
#include <sys/resource.h>

std::string output_file;
int target_keys = -1;

int sle_main(int argc, char* argv[])
{
    int cpu_limit = -1;
    int64_t data_limit = -1;
    bool extended = true;
    std::string mutability;
    std::string graph;
    std::string clique;
    int dac12_enc = 0;
    int random_ins = 0;
    int ilp_encoder = 0;
    int toc13_enc = 0;
    std::string fault_impact_file;
    double key_fraction = 0.0;
    int mux_enc = 0;
    int iolts14_enc = 0;

    int c;
    while ((c = getopt (argc, argv, "ihc:rm:o:k:eM:dg:C:f:ItT:s")) != -1) {
        switch (c) {
            case 'h':
                return sle_usage(argv[0]);
                break;
            case 'i':
                iolts14_enc = 1;
                break;
            case 't':
                toc13_enc = 1;
                break;
            case 's':
                mux_enc = 1;
                break;
            case 'T':
                fault_impact_file = optarg;
                break;
            case 'c':
                cpu_limit = atoi(optarg);
                break;
            case 'm':
                data_limit = ((int64_t) atoi(optarg)) * ((int64_t)1048576);
                break;
            case 'o':
                output_file = optarg;
                break;
            case 'k':
                target_keys = atoi(optarg);
                break;
            case 'f':
                key_fraction = atof(optarg);
                break;
            case 'M':
                mutability = optarg;
                break;
            case 'g':
                graph = optarg;
                break;
            case 'C':
                clique = optarg;
                break;
            case 'e':
                extended = !extended;
                break;
            case 'd':
                dac12_enc = 1;
                break;
            case 'I':
                ilp_encoder = 1;
                break;
            case 'r':
                random_ins = 1;
                break;
            default:
                break;
        }
    }


    // check if we got a test article.
    if(optind == argc || optind != argc-1) {
        return sle_usage(argv[0]);
    }

    if(cpu_limit != -1) {
        setup_cpux_handler();

        struct rlimit rl;
        rl.rlim_cur = cpu_limit;
        setrlimit(RLIMIT_CPU, &rl);
    }

    if(data_limit != -1) {
        struct rlimit rl;
        rl.rlim_cur = rl.rlim_max = data_limit;
        if(setrlimit(RLIMIT_AS, &rl) != 0) {
            std::cerr << "trouble setting data limit." << std::endl;
        }
    }

    yyin = fopen(argv[optind], "rt");
    if(yyin == NULL) {
        perror(argv[optind]);
        return 1;
    }

    if(yyparse() == 0) {
        using namespace ast_n;

        if(iolts14_enc) {
            if(key_fraction == 0.0) {
                std::cerr << "Error: must specify fraction to insert. " << std::endl;
                exit(1);
            }
            ckt_n::toc13enc_t tenc(*statements, key_fraction);
            tenc.encodeIOLTS14();
            if(output_file.size() == 0) {
                tenc.write(std::cout);
            } else {
                std::ofstream fout(output_file.c_str());
                tenc.write(fout);
            }
        } else if(toc13_enc) {
            if(key_fraction == 0.0) {
                std::cerr << "Error: must specify fraction to insert. " << std::endl;
                exit(1);
            }
            ckt_n::toc13enc_t tenc(*statements, key_fraction);
            if(fault_impact_file.size() == 0) {
                tenc.evaluateFaultImpact(5000);
            } else {
                tenc.readFaultImpact(fault_impact_file);
            }
            if(mux_enc) {
                tenc.encodeMuxes();
            } else {
                tenc.encodeXORs();
            }
            if(output_file.size() == 0) {
                tenc.write(std::cout);
            } else {
                std::ofstream fout(output_file.c_str());
                tenc.write(fout);
            }

        } else if(ilp_encoder) {
#ifdef CPLEX_ENABLED
            if(key_fraction == 0.0) {
                std::cerr << "Error: must specify fraction to insert. " << std::endl;
                exit(1);
            }
            ckt_n::ilp_encoder_t ioenc(*statements, key_fraction);
            ioenc.encode3();
            if(output_file.size() == 0) {
                ioenc.write(std::cout);
            } else {
                std::ofstream fout(output_file.c_str());
                ioenc.write(fout);
            }
#else
            std::cerr << "Error: can't run ILP encoder because sle was not compiled with CPLEX." << std::endl;
#endif
        } else if(dac12_enc) {
            if(graph.size() == 0) {
                std::cerr << "Error: must specify graph filename." << std::endl;
                exit(1);
            }
            if(clique.size() == 0) {
                std::cerr << "Error: must specify clique filename." << std::endl;
                exit(1);
            }
            if(output_file.size() == 0) {
                std::cerr << "Error: must specify output file." << std::endl;
                exit(1);
            }
            if(key_fraction == 0.0) {
                std::cerr << "Error: must specify fraction to insert. " << std::endl;
                exit(1);
            }
            ckt_n::dac12enc_t denc(*statements, graph, clique, key_fraction);
            std::ofstream fout(output_file.c_str());
            denc.write(fout);
        } else if(mutability.size()) {
            ckt_n::ckt_t ckt(*statements);

            std::ofstream fout(mutability.c_str());
            ckt_n::mutability_analysis_t mut(ckt, fout);
            mut.analyze();
            fout.close();

            std::cout << "finished" << std::endl;
        } else if(random_ins == 1) {
            if(target_keys == -1 && key_fraction == 0.0) {
                std::cerr << "Error, must specify target number of keys with -k <keys> or -f <fraction> flag." << std::endl;
            }
            if (output_file.size() == 0) {
                std::cerr << "Error: must specific output file." << std::endl;
            } 

            ckt_n::ckt_t ckt(*statements);
            if(key_fraction != 0.0) {
                target_keys = (int) (ckt.num_gates() * key_fraction + 0.5);
            }
            std::ofstream fout(output_file.c_str());
            random_insert(ckt, target_keys, fout);
            fout << ckt << std::endl;
        } else {
            std::cout << "Error! Must select an encoding scheme. " << std::endl;
            exit(1);
        }
    }


    return 0;
}

int sle_usage(const char* progname)
{

    std::cout << "Usage: " << std::endl;
    std::cout << "\t" << progname << " -r -k <keys> -o <bench-out> <bench-in>: to do random insertion." << std::endl;
    std::cout << "\t" << progname << " -r -f <fraction> -o <bench-out> <bench-in>: to do random insertion." << std::endl;
    std::cout << "\t" << progname << " -i -f <fraction> -o <bench-out> <bench-in> : to encode using the IOLTS technique." << std::endl;
    std::cout << "\t" << progname << " -M <enc> <bench-in>: to compute mutability graph and dump it to a file." << std::endl;
    std::cout << "\t" << progname << " -d -g <graph> -C  <clique> -o <bench-out> <bench-in> : to do DAC'12 encryption." << std::endl;
    std::cout << "\t" << progname << " -t -f <fraction> -o <bench-out> <bench-in> : to encode using fault impact [Toc'13/XOR]." << std::endl;
    std::cout << "\t" << progname << " -t -f <fraction> -s -o <bench-out> <bench-in> : to encode using fault impact [Toc'13/MUX]." << std::endl;
    return 0;
}


// end of the file.
// 
//
//
