## OPTIMIZATION 1NAIVE VERSION
# USES STRIPED PARTITIONS
# USES A STACK
# USES ORDERED PARTITIONS
# USES A CACHE OF NON FDS

import csv
import sys
import copy
import random
import argparse
import time
from ae_libs.enumerations import LectiveEnum
from ae_libs.boolean_tree import BooleanTree
from ae_libs.fd_tree import FDTree
from ae_libs.fca import FormalContext, next_closure, PreClosure, fast_next_closure
from ae_libs import read_csv
from itertools import product
from collections import defaultdict
from functools import reduce

def mine_fds(ctx, closure):
    U = set(ctx.M)
    fdt = FDTree(U)
    
    A = closure(set([]))

    if bool(A):
        fdt.add_fd(set([]), A)
    i = max(ctx.M)

    while len(A) < len(ctx.M):
        
        for j in reversed(ctx.M):
            if j in A:
                A.remove(j)
            else:
                B = fdt.l_close(A.union([j]))
                if not bool(B-A) or j <= min(B-A):
                    A = B
                    i = j
                    break
        AII = closure(A)
        # print sorted(A), sorted(AII)
        if len(A) < len(AII):
            fdt.add_fd(A, AII-A)
        if not bool(AII-A) or i <= min(AII-A):
            A = AII
            i = max(ctx.M)
        else:
            A = A.intersection(set([i for i in range(i+1)]))
    return fdt

def match(t1, t2):
    return set([i for i, (a,b) in enumerate(zip(tuples[t1], tuples[t2])) if a==b ])

def check(X, XJJ, tuples, n_atts, cache, rand_tuples):
    '''
    Linear check an FD X -> XJJ
    '''
    # print(X, XJJ)
    signatures = {}
    preintent = sorted(X)
    AII = sorted(XJJ-X)
    
    nt = len(tuples)-1

    for h in range(len(tuples)):
        ti = rand_tuples[h]
        row = tuples[ti]
        # left = tuple((row[att] for att in preintent))
        left = ','.join((str(row[att]) for att in preintent))
        tj = signatures.get(left, None)

        if tj is None:
            signatures[left] = ti
        elif any(row[att] != tuples[tj][att] for att in AII):
            cache.append(set(att for att in range(n_atts) if row[att]==tuples[tj][att]))
            to_remove = [att for att in AII if att not in cache[-1]]
            for x in to_remove:
                AII.remove(x)
            if not bool(AII):
                break
    return X.union(AII)

def attribute_exploration_pps(tuples):
    U = range(len(tuples[0])) # Attributes
    n_atts = len(U)
    m_prime = [set([]) for i in range(len(U))]
    g_prime = []
    
    rand_tuples = list(range(len(tuples)))
    # random.shuffle(rand_tuples)
    rand_tuples.sort(key=lambda i: len(set(tuples[i])))

    fctx = FormalContext(g_prime, m_prime)

    m_prime.append(set([])) # THIS SHOULD BE AFTER DECLARING THE FORMAL CONTEXT

    representations = [[row[j] for row in tuples] for j in U]

    # ATTRIBUTE ORDERING
    order = [(len(set(r)), ri) for ri, r in enumerate(representations)]
    order.sort(key=lambda k: k[0], reverse=False)
    #print (order)
    order = {j[1]:i for i,j in enumerate(order)} #Original order -> new order
    inv_order = {i:j for j,i in order.items()}
    for ti, t in enumerate(tuples):
        tuples[ti] = [t[inv_order[i]] for i in range(len(t))]
    
    # # END ORDERING

    # VARIABLES FOR FAST STACKED NEXT CLOSURE
    Mjs = [set() for i in range(n_atts)]
    stack = [[None, m_prime[-1]],[None, set([]), Mjs]]

    # INITIALIZATION VARIABLES
    X = set([])
    fdt = FDTree(U)
    m_i = -1 # WE START WITH THE EMPTY INTENT REPRESENTED BY THIS
    
    # COUNTERS TO KEEP SOME PERFORMANCE STATISTICS
    cycles = 0
    cycles2 = 0
    avoided_closures = 0
    ncls = 0
    while X != U:
        cycles += 1
        if cycles%1000 == 0:
            print ("\rFDs:{}/{}/{}/{}/{} - {: <100}".format(fdt.n_fds, cycles, cycles2, len(g_prime), (sum([len(mp) for mp in m_prime]))/len(m_prime), ','.join(map(str, sorted(X)))), end='') #stack
            sys.stdout.flush()

        XJ = stack[-2][1].intersection(m_prime[m_i])
        if bool(XJ):
            # XJJ = reduce(set.intersection, (g_prime[g] for g in XJ))
            XJJ = set.intersection(*[g_prime[g] for g in XJ])
            if len(XJ) == 1:
                XJJ = set(XJJ)
        else:
            XJJ = set(U)

        # AT THIS POINT WE HAVE XJJ WHICH IS OUR ESTIMATION OF THE CLOSURE
        # USING THE REPRESENTATION CONTEXT CALCULATED SO FAR
        # THE ACTUAL CLOSURE SHOULD BE XSS, HOWEVER IF 
        # X = XJJ WE KNOW THAT XSS = XJJ AND WE CAN AVOID ITS
        # CALCULATION

        XSS = None
        n_x = len(X)

        avoided_closures += n_x == len(XJJ)

        while n_x < len(XJJ): # CHECKS WHETHER X==XJJ

            cycles2 += 1

            if XSS is None:
                cache = []
                XSS = check(X, XJJ, tuples, n_atts, cache, rand_tuples)
                cache.sort(key=len)
            
            if len(XJJ) == len(XSS):
                fdt.add_fd(X, XJJ)
                print(X,XJJ, m_i)
                # print(fdt.fds)
                break
            else:
                gp = cache.pop()

                n_gp = len(g_prime)
                XJ.add(n_gp)
                for i in stack[1:]:
                    i[1].add(n_gp)
                for x in gp:
                    m_prime[x].add(n_gp)

                g_prime.append(gp)
                XJJ.intersection_update(gp)

        new_atts = XJJ - X

        if not bool(new_atts) or m_i <= min(new_atts):
            m_i = U[-1]
            X = XJJ
        else:
            # print(stack)
            stack[-2][2][m_i] = XJJ
            X.difference_update([m for m in X if m > m_i])

        stack[-1][1] = XJ

        X, m_i,c = fast_next_closure(X, U, fdt.l_close, m_i, stack)

        ncls += c

        stack[-1][0] = m_i
        
    # print ('--')
    # for g in g_prime:
    #    print (g)

    L = list(fdt.read_fds())
    print ("\nNUMBER OF FDS:{}".format(len(L)))
    print ("SAMPLING CONTEXT SIZE:{}".format(len(g_prime)))
    print ("CYCLES:",cycles)
    print ("GOOD CLOSURES:", avoided_closures)
    print ("Closures:", ncls)
    print(fdt.recursions)


if __name__ == "__main__":
    
    __parser__ = argparse.ArgumentParser(description='FD Miner - Sampling-based Version')
    __parser__.add_argument('database', metavar='database_path', type=str, help='path to the formal database')
    __parser__.add_argument('-s', '--separator', metavar='separator', type=str, help='Cell separator in each row', default=',')
    # __parser__.add_argument('-p', '--use_patterns', help='Use Pattern Structures for DB', action='store_true')
    __parser__.add_argument('-i', '--ignore_headers', help='Ignore Headers', action='store_true')
    args = __parser__.parse_args()

    tuples = read_csv(args.database, separator=args.separator)
    
    t0 = time.time()
    attribute_exploration_pps(tuples)
    print ("TIME: {}s".format(time.time()-t0))

