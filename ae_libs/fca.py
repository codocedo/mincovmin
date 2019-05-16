import copy
from collections import defaultdict

class FormalContext(object):
    def __init__(self, g_prime, m_prime):
        self.g_prime = g_prime
        self.m_prime = m_prime
        self.M = list(range(len(self.m_prime)))
    
    # @property
    # def M(self):
    #     return 

    
    def derive_intent(self, intent):
        '''
        returns intent'
        '''
        if bool(intent):
            out = reduce(set.intersection, (self.m_prime[x] for x in intent))
            if len(intent) == 1:
                out = copy.copy(out)
            return out
        return set(range(len(self.g_prime)))

    def derive_extent(self, extent):
        '''
        return extent'
        '''
        if bool(extent):
            out = reduce(set.intersection, (self.g_prime[t] for t in extent))
            if len(extent) == 1:
                out = copy.copy(out)
            return out
        return set(range(len(self.m_prime)))

        

    def closed_set(self, X):
        return self.derive_extent(self.derive_intent(X))
    

def fast_next_closure(A, M, closure, m_i=None, stack=None):
    closures = 0
    for m in reversed(M):
        if m in A:
            A.remove(m)
            if m == stack[-1][0]:
                stack.pop()
        else:
            Mjs = stack[-1][2]
            
            if all(j in A for j in Mjs[m] if j < m):
                B = closure(A.union([m]))
                closures += 1
                D = B-A
                if not bool(D) or m <= min(D):
                    stack.append([None, set([]), list(Mjs)])
                    return B, m, closures
                else:
                    Mjs[m] = B
    return M, M[-1], closures

def next_closure(A, M, closure,  m_i=None, stack=None):
    # if m_i is None:
    #     m_i = M[-1]
    closures = 0
    for m in reversed(M):
        # if m > m_i:
        #     continue
        if m in A:
            A.remove(m)
            if m == stack[-1][0]:
                stack.pop()
        else:
            B = closure(A.union([m]))
            closures += 1
            # print('\t', B)
            if not bool(B-A) or m <= min(B-A):
                stack.append([None, set([])])
                return B, m, closures
    return M, M[-1], closures

class PreClosure(object):
    def __init__(self, L, n_atts):
        self.L = L
        self.n_atts = n_atts

    def l_close(self, pat):
        # print 'LCLOSE', pat, self.L
        newpat = set(pat)
        
        complement = set([])
        while True:
            if len(newpat) == self.n_atts:
                break
            subparts = [con for ant, con in self.L if len(ant) < len(newpat) and ant.issubset(newpat)]
            if bool(subparts):
                complement = reduce(set.union, subparts)
                if complement.issubset(newpat):
                    break
                else:
                    newpat.update(complement)
            else:
                break
        return newpat