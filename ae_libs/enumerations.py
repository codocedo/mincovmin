
class LectiveEnum(object):
    # 4, 3, 34, 2, 24, 23, 234, 1, 14, 13, 134, 12, 124, 123, 1234
    def __init__(self, n):
        self.n = n
        self.current = None
        self.stack = []
    
    def next(self, current):
        
        # current = copy.copy(crt)
        # if current is None:
        #     current = []
        # NORMALLY, WE'LL TRY TO ADD A NEW ELEMENT N ON THE RIGHT
        # UNLESS THE LAST ELEMENT OF THE CURRENT ENUMERATION IS N
        # 12 -> 124
        if not bool(current) or current[-1] != self.n:
            self.stack.append(self.n)
            current.append(self.n)
        # IF THE THE LAST ELEMENT IS INDEED N, WE'LL TRY TO LOWER IT
        # 14-> 13
        else:
            current[-1] -= 1
            self.stack[-1] = current[-1]
            # IT MAY BE THAT LOWERING IT CAUSES A SIDE EFFECT
            # 134 -> 133
            # IN THIS CASE, WE'LL REMOVE THE LAST ELEMENT AND DECREASE THE SECOND THE LAST ELEMENT
            # NOTICE THAT THIS SHOULD CASCADE UNTIL CONVERGENCE
            # 234 -> 233 -> 22 -> 1
            while len(current) > 1 and current[-1] <= current[-2]:
                #current = current[:-1]
                del current[len(current)-1]
                current[-1] -= 1
                self.stack[-1] = current[-1]
        # if current == [-1]:
        #     return None
        # print len(current)-len(self.stack)
        for i in range(len(self.stack)-len(current)):
            #print self.stack,'pop',
            self.stack.pop()
            self.stack[-1] = current[-1]
            #print self.stack
        return current
    
    def last(self, crt):
        crt.extend(range(crt[-1]+1, self.n+1))
        return crt

    # def next(self):
    #     if self.current is None:
    #         self.current = []
    #     # NORMALLY, WE'LL TRY TO ADD A NEW ELEMENT N ON THE RIGHT
    #     # UNLESS THE LAST ELEMENT OF THE CURRENT ENUMERATION IS N
    #     # 12 -> 124
    #     if not bool(self.current) or self.current[-1] != self.n:
    #         self.current.append(self.n)
    #     # IF THE THE LAST ELEMENT IS INDEED N, WE'LL TRY TO LOWER IT
    #     # 14-> 13
    #     else:
    #         self.current[-1] -= 1 
    #         # IT MAY BE THAT LOWERING IT CAUSES A SIDE EFFECT
    #         # 134 -> 133
    #         # IN THIS CASE, WE'LL REMOVE THE LAST ELEMENT AND DECREASE THE SECOND THE LAST ELEMENT
    #         # NOTICE THAT THIS SHOULD CASCADE UNTIL CONVERGENCE
    #         # 234 -> 233 -> 22 -> 1
    #         while len(self.current) > 1 and self.current[-1] <= self.current[-2]:
    #             self.current = self.current[:-1]
    #             self.current[-1] -= 1
    #     if self.current == [-1]:
    #         self.current = None
    #     return self.current
    def skip_level(self):
        self.current.append(self.current[-1])

    def compare(self, el1, el2):
        return el1.issubset(el2) or tuple(sorted(el2)) < tuple(sorted(el1))
