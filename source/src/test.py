#! /usr/bin/python3

import subprocess
import os
import sys
import argparse
from multiprocessing import Pool
import time

tests = [
    ('../../benchmarks/toc13mux/c432_enc25.bench', '../../benchmarks/original/c432.bench'),
    ('../../benchmarks/rnd/c499_enc05.bench', '../../benchmarks/original/c499.bench'),
    ('../../benchmarks/toc13xor/c432_enc50.bench', '../../benchmarks/original/c432.bench'),
    ('../../benchmarks/toc13xor/i7_enc05.bench', '../../benchmarks/original/i7.bench'),
    ('../../benchmarks/toc13mux/c880_enc50.bench', '../../benchmarks/original/c880.bench'),
    ('../../benchmarks/rnd/i8_enc05.bench', '../../benchmarks/original/i8.bench'),
    ('../../benchmarks/dac12/i9_enc05.bench', '../../benchmarks/original/i9.bench'),
    ('../../benchmarks/toc13xor/c5315_enc05.bench', '../../benchmarks/original/c5315.bench'),
    ('../../benchmarks/toc13mux/k2_enc10.bench', '../../benchmarks/original/k2.bench'),
    ('../../benchmarks/toc13mux/apex4_enc05.bench', '../../benchmarks/original/apex4.bench'),
    ('../../benchmarks/iolts14/apex4_enc10.bench', '../../benchmarks/original/apex4.bench'),
    ('../../benchmarks/toc13xor/i8_enc10.bench', '../../benchmarks/original/i8.bench'),
    ('../../benchmarks/dtc10lut/c880_enc.bench', '../../benchmarks/original/c880.bench'),
    ('../../benchmarks/dac12/apex2_enc25.bench', '../../benchmarks/original/apex2.bench'),
    ('../../benchmarks/dac12/dalu_enc10.bench', '../../benchmarks/original/dalu.bench'),
    ('../../benchmarks/toc13mux/ex1010_enc25.bench', '../../benchmarks/original/ex1010.bench'),
    ('../../benchmarks/dac12/ex1010_enc05.bench', '../../benchmarks/original/ex1010.bench'),
    ('../../benchmarks/toc13xor/i4_enc50.bench', '../../benchmarks/original/i4.bench'),
    ('../../benchmarks/dac12/i8_enc25.bench', '../../benchmarks/original/i8.bench'),
]
SHORT_TESTS=10

def run_sld(test):
    out = subprocess.check_output(['./sld'] + list(test))
    lines = [l.strip() for l in out.decode('utf-8').split('\n') if len(l.strip()) > 0]
    key = lines[-2]
    assert key.startswith('key=')
    return (lines[-2], lines[-1], lines)

def run_lcmp(test, key):
    out = subprocess.check_output(['./lcmp', test[1], test[0], key])
    result = out.decode('utf-8').strip()
    return result

def run_test(test):
    (key, stats, lines) = run_sld(test)
    result = run_lcmp(test, key)
    return (result, stats)

def run_specific_test(test):
    (key, stats, lines) = run_sld(test)
    result = run_lcmp(test, key)
    print ('OUTPUT:')
    print ('-------')
    print ('\n'.join(lines))
    print ()
    print ('RESULT:')
    print ('-------')
    print (result)

def get_cpu_time(stats):
    words = [s.strip() for s in stats.split(';')]
    assert words[3].startswith('cpu_time=')
    return float(words[3].split('=')[1])

def run_one_test(t):
    (result, stats) = run_test(t)
    cpu_time = get_cpu_time(stats)
    test = os.path.basename(t[0])
    return (test, cpu_time, result)

def run_tests(num_tests):

    good = True
    total_time = 0.0
    with Pool() as p:
        start_time = time.time()
        results = p.map(run_one_test, tests[:num_tests])
        for r in results:
            (test, cpu_time, result) = r
            print ('%-20s [%8.2f] %-10s' % (test, cpu_time, result))
            if result != 'equivalent':
                good = False
            total_time += cpu_time
        pass_str = 'PASS' if good else 'FAIL'
        end_time = time.time()
        wallclock_time = end_time - start_time
        print ('-'*(20+8+10+4))
        print ('%-20s [%8.2f] %-10s' % ('TOTAL CPU TIME:', total_time, pass_str))
        print ('%-20s [%8.2f] %-10s' % ('WALLCLOCK TIME:', wallclock_time, pass_str))
        return (0 if good else 1)

def main():
    parser = argparse.ArgumentParser()
    suite_choices = ['short', 'all'] + [str(i) for i in range(1, len(tests)+1)]
    parser.add_argument('tests', default='short', choices=suite_choices)
    args = parser.parse_args()

    if args.tests == 'short':
        run_tests(SHORT_TESTS)
    elif args.tests == 'all':
        run_tests(len(tests))
    else:
        run_specific_test(tests[int(args.tests)-1])

if __name__ == '__main__':
    exit_code = main()
    sys.exit(exit_code)
