#!/usr/bin/env python
#file Math24Game.py

""" Provides Math 24 game cards and generators.



Revision History

12/21/2006 Jason Gross: Classes written
"""

from JMath import flatten, rearrangements
from JMath.polynomial import Polynomial
from random import Random

class Solution(object):
    _LIST_TYPES = (list, tuple)
    
    def __new__(cls, sol, unique=False):
        """
        
        sol - if list, in form of [numList, opList, typeNum]
        
        if numList is [a, b, c, d]
        typeNum:
        0 - a op b = s1, c op d = s2, s1 op s2 = 24
        1 - a op b = s1, s1 op c = s2, s2 op d = 24
        2 - a op b = s1, c op s1 = s2, s2 op d = 24
        3 - a op b = s1, s1 op c = s2, d op s2 = 24
        4 - a op b = s1, c op s1 = s2, d op s2 = 24
        """
        self = object.__new__(cls)
        if type(sol) in Solution._LIST_TYPES:
            self._orig_nums = tuple(sol[0])
            self._type_num = sol[2]
            self._ops = tuple([i for i in sol[1]])
            self._nums = tuple([tuple([num for num in line]) for line in Solution._make_sol_list(sol[0], sol[2], sol[1])])
        elif type(sol) == Solution:
            self._orig_nums = tuple([i for i in sol._orig_nums])
            self._type_num = sol._type_num
            self._ops = tuple([i for i in sol._ops])
            self._nums = tuple([i for i in sol._nums])
        self._unique = unique
        self._nums = [[num for num in line] for line in self._nums]
        for line in range(len(self._nums)):
            if self._ops[line] in '+*': 
                f2 = self._nums[line][:2]
                f2.sort()
                self._nums[line][:2] = f2
        if self._type_num == 0:
            if cmp(str(self._nums[0]), str(self._nums[1])) > 0:
                self._nums[0], self._nums[1] = self._nums[1], self._nums[0]
        self._nums = self._nums = tuple([tuple([num for num in line]) for line in self._nums])
        return self
    
    def __eq__(self, other):
        if self._unique: return self.isSame(other)
        else: return self._type_num == other._type_num and self._ops == other._ops and self._nums == other._nums
    
    def __ne__(self, other): 
        return not (self == other)
        
    def __cmp__(self, other):
        if self == other: return cmp(1, 1)
        return cmp(str(self), str(other))
    
    def isSame(self, other):
        if self._type_num == other._type_num and self._ops == other._ops and self._nums == other._nums: return True
        if (self.works() and not other.works()) or (other.works() and not self.works()): return False
        if set(self._orig_nums) != set(other._orig_nums): return False
        if set(self._ops) != set(other._ops): return False
        if self._ops[-1] != other._ops[-1]: return False
        if self._nums[-1] != other._nums[-1]: return False
        if all([(i in '+*') for i in self._ops[:2]]): return True
        if self._ops[:2] == other._ops[:2] and self._nums[0] == other._nums[1] and self._nums[1] == other._nums[0]: return True
        return False
        
    def works(self):
        for line in self._nums:
            for num in line:
                if num == None or num != int(num) or num < 0: return False
        return self._nums[-1][-1] == 24
        
    def __str__(self):
        return '\n'.join([str(self._nums[line][0]) + ' ' + self._ops[line] + ' ' + str(self._nums[line][1]) + ' = ' + str(self._nums[line][2]) for line in range(len(self._ops))])
    
    def __repr__(self):
        return '\n'.join([repr(self._nums[line][0]) + ' ' + self._ops[line] + ' ' + repr(self._nums[line][1]) + ' = ' + repr(self._nums[line][2]) for line in range(len(self._ops))])

    def _eval_op(cls, num1, op, num2):
        if '+' in op: return int(num1 + num2)
        elif '-' in op: return int(num1 - num2)
        elif '*' in op: return int(num1 * num2)
        elif (1.0 * num1) / num2 == num1 / num2: return int(num1 / num2)
        else: return (1.0 * num1) / num2
    _eval_op = classmethod(_eval_op)
        
    def _make_sol_list(cls, nums, typeNum, opList):
        try:
            rtn = [[None, None, None] for i in range(3)]
            rtn[0] = [nums[0], nums[1], Solution._eval_op(nums[0], opList[0], nums[1])]
            if min(rtn[0]) < 0 or rtn[0][-1] != int(rtn[0][-1]): return [[None, None, None]] * 3
            
            if typeNum in (0, 2, 4): rtn[1][0] = nums[2]
            else: rtn[1][0] = rtn[0][2]
            if typeNum in (1, 3): rtn[1][1] = nums[2]
            elif typeNum == 0: rtn[1][1] = nums[3]
            else: rtn[1][1] = rtn[0][2]
            rtn[1][2] = Solution._eval_op(rtn[1][0], opList[1], rtn[1][1])
            if min(rtn[1]) < 0 or rtn[1][-1] != int(rtn[1][-1]): return [[None, None, None]] * 3
            
            if typeNum in (3, 4): rtn[2][0] = nums[3]
            elif typeNum == 0: rtn[2][0] = rtn[0][2]
            else: rtn[2][0] = rtn[1][2]
            if typeNum in (1, 2): rtn[2][1] = nums[3]
            else: rtn[2][1] = rtn[1][2]
            rtn[2][2] = Solution._eval_op(rtn[2][0], opList[2], rtn[2][1])
            if min(rtn[2]) < 0 or rtn[2][-1] != int(rtn[2][-1]): return [[None, None, None]] * 3
            
            return rtn
        except ZeroDivisionError:
            return [[None, None, None]] * 3            
    _make_sol_list = classmethod(_make_sol_list)
    
class RegularCard(object):
    """ Represents a Math 24 card with four numbers. """
    _LIST_TYPES = (list, tuple)
    
    def __new__(cls, num1, num2=None, num3=None, num4=None):
        self = object.__new__(cls)
        if type(num1) in RegularCard._LIST_TYPES: self._nums = tuple([i for i in num1])
        elif type(num1) == RegularCard: self._nums = tuple([i for i in num1._nums])
        else: self._nums = (num1, num2, num3, num4)
        self._solve()
        return self
    
    def _get_nums(self): return self._nums
    Numbers = property(_get_nums)
    
    def works(self): return len(self._sols)
    
    def _solve(self):
        self._sols = set()
        self._unique_sols = set()
        for nums in rearrangements(self._nums):
            for type_num in range(5):
                for op1 in '+-*/':
                    for op2 in '+-*/':
                        for op3 in '+-*/':
                            cur_sol = Solution((nums, (op1, op2, op3), type_num), False)
                            if cur_sol.works():
                                self._sols.add(cur_sol)
                                self._unique_sols.add(Solution(cur_sol, True))
        self._sols = list(set([str(i) for i in self._sols]))
        self._unique_sols = list(set([str(i) for i in self._unique_sols]))
        self._sols.sort()
        self._unique_sols.sort()
        self._sols = tuple(self._sols)
        self._unique_sols = tuple(self._unique_sols)
    
    def _get_sols(self): return '\n \n'.join([str(i) for i in self._sols])
    def _get_unique_sols(self): return '\n \n'.join([str(i) for i in self._unique_sols])
    Solutions = property(_get_sols)
    UniqueSolutions = property(_get_unique_sols)

    def __str__(self):
        return 'RegularCard(' + ', '.join([str(i) for i in self._nums]) + ')'
    
    def __repr__(self):
        return 'RegularCard(' + ', '.join([repr(i) for i in self._nums]) + ')'
    
    def makeRandomCard(cls, must_work=True, rnd=None):
        if rnd == None:
            rnd = Random()
            rnd.seed()
        nums = tuple([tuple(rnd.sample(range(1, 25), 24)) for i in range(4)])
        i = 0
        for n1 in nums[0]:
            for n2 in nums[1]:
                for n3 in nums[2]:
                    for n4 in nums[3]:
                        cur_card = RegularCard(n1, n2, n3, n4)
                        if cur_card.works() or not must_work: return cur_card
        return None
    makeRandomCard = classmethod(makeRandomCard)
##            
##a=RegularCard.makeRandomCard(True,Random(2))
##print a
##b = raw_input("")
##print a.UniqueSolutions