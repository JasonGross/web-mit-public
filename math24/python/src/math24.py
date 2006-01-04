import random
import os
import sys
def cls():
    if sys.platform in ('linux-i386', 'linux2'):
        os.system('clear')
    elif sys.platform in ('win32', 'dos') or sys.platform.startswith('ms-dos'):
        os.system('cls')
def xor(*values):
    works = False
    for i in values:
        if works and i: return False
        works = works or i
    return works
def solveCard(numbers, printSols = True, unique = True):
    c = card(numbers, unique)
    c.solve()
    if printSols: c.printSols(unique)
    else: return c.solutions(unique)
class card(object):
    cardTypes = {4: 'Regular', 6: 'Variable', 12: 'Wheel', 16: 'Quad', 'Regular': 4, 'Variable': 6, 'Wheel': 12, 'Quad': 16}
    def __init__(self, numbers, unique = False):
        if type(numbers) == card: self.numbers = list(numbers.numbers)
        else: self.numbers = list(numbers)
        self.cardType = card.cardTypes[len(self.numbers)]
        self.unique = unique
        self.sols = None
        self.sols2 = None
    def cardWorks(self, variable = None, resolve = True):
        if resolve: self.solve(variable)
        if self.cardType == 'Regular' or self.cardType == 'Quad':
            return len(self.sols) > 0
        elif variable != None:
            if type(variable) in (list, tuple):
                return [self.cardWorks(i, resolve) for i in variable]
            else:
                return len(self.sols[variable][0]) > 0
        else:
            return max([len(self.sols[i][0]) for i in self.sols]) > 0
    def solve(self, variable = None):
        if self.cardType == 'Regular':
            self.sols = []
            for i in set(self.numbers):
                n2 = list(self.numbers)
                n2.remove(i)
                for j in set(n2):
                    n3 = list(self.numbers)
                    n3.remove(i)
                    n3.remove(j)
                    for k in set(n3):
                        n4 = list(self.numbers)
                        n4.remove(i)
                        n4.remove(j)
                        n4.remove(k)
                        for l in set(n4):
                            for op1 in ('+', '-', '/', '*'):
                                for op2 in ('+', '-', '/', '*'):
                                    for op3 in ('+', '-', '/', '*'):
                                        try:
                                            a1 = eval(str(i) + op1 + str(j))
                                            for np3 in (a1, k):
                                                npc4 = [a1, k, l]
                                                npc4.remove(np3)
                                                for np4 in npc4:
                                                    try:
                                                        a2 = eval(str(np3) + op2 + str(np4))
                                                        npc6 = [a1, a2, k, l]
                                                        npc6.remove(np3)
                                                        npc6.remove(np4)
                                                        for np6 in npc6:
                                                            npc7 = list(npc6)
                                                            npc7.remove(np6)
                                                            for np7 in npc7:
                                                                try:
                                                                    a3 = eval(str(np6) + op3 + str(np7))
                                                                    if a3 == 24 and a1 >= 0 and a2 >= 0:
                                                                        good = True
                                                                        for tester in ((i, op1, j), (np3, op2, np4), (np6, op3, np7)):
                                                                            if tester[1] == '/' and (tester[0] / tester[2]) * tester[2] != tester[0]:
                                                                                good = False
                                                                                break
                                                                        if good:
                                                                            sol = str(i) + ' ' + op1 + ' ' + str(j) + ' = ' + str(a1) + '\n' + \
                                                                                  str(np3) + ' ' + op2 + ' ' + str(np4) + ' = ' + str(a2) + '\n' + \
                                                                                  str(np6) + ' ' + op3 + ' ' + str(np7) + ' = ' + str(a3)
                                                                            if sol not in self.sols: self.sols.append(sol)
                                                                except ZeroDivisionError:
                                                                    pass                                                                                
                                                    except ZeroDivisionError:
                                                        pass    
                                        except ZeroDivisionError:
                                            pass
            self.sols = [i.replace('/', '÷').replace('*', '×') for i in self.sols]
            self.sols.sort()
            self.sols2 = []
            for i in self.sols:
                add = True
                eq = i.split('\n')
                eq = [j.split(' ') for j in eq]
                for j in range(len(eq)):
                    if eq[j][1] == '÷' and j != 2 and eq[j][2] == '1': eq[j][1] = '×'
                    if eq[j][1] in ('+', '×') and int(eq[j][0]) < int(eq[j][2]):
                        eq[j][0], eq[j][2] = eq[j][2], eq[j][0]
                eq = '\n'.join([' '.join(j) for j in eq])
                for j in self.sols2:
                    if self.isEq(eq, j):
                        add = False
                        break
                if add: self.sols2.append(eq)
        elif self.cardType == 'Variable':
            if variable == None:
                self.solve([i + 1 for i in range(9)])
            elif type(variable) == list or type(variable) == tuple:
                for i in variable: self.solve(i)
            elif type(variable) == int:
                if self.sols == None: self.sols = {}
                if self.sols2 == None: self.sols2 = {}
                c1 = card([self.numbers[i] for i in range(3)] + [variable])
                c2 = card([self.numbers[i] for i in range(3, 6)] + [variable])
                if c1.cardWorks() and c2.cardWorks():
                    self.sols[variable] = (c1.sols, c2.sols)
                    self.sols2[variable] = (c1.sols2, c2.sols2)
                else:
                    self.sols[variable] = ([], [])
                    self.sols2[variable] = ([], [])
        elif self.cardType == 'Wheel':
            if variable == None:
                self.solve([i + 1 for i in range(9)])
            elif type(variable) == list or type(variable) == tuple:
                for i in variable: self.solve(i)
            elif type(variable) == int:
                if self.sols == None: self.sols = {}
                if self.sols2 == None: self.sols2 = {}
                c1 = card([self.numbers[i] for i in range(3)] + [variable])
                c2 = card([self.numbers[i] for i in range(3, 6)] + [variable])
                c3 = card([self.numbers[i] for i in range(6, 9)] + [variable])
                c4 = card([self.numbers[i] for i in range(9, 12)] + [variable])
                if c1.cardWorks() and c2.cardWorks() and c3.cardWorks() and c4.cardWorks():
                    self.sols[variable] = (c1.sols, c2.sols, c3.sols, c4.sols)
                    self.sols2[variable] = (c1.sols2, c2.sols2, c3.sols2, c4.sols2)
                else:
                    self.sols[variable] = ([], [], [], [])
                    self.sols2[variable] = ([], [], [], [])
        elif self.cardType == 'Quad':
            self.cardnum = None
            self.sols = []
            self.sols2 = []
            c = [card([self.numbers[i] for i in range(4 * j, 4* j + 4)]) for j in range(3)]
            if xor(*[i.cardWorks() for i in c]):
                for i in range(4):
                    if c[i].cardWorks(resolve = False):
                        self.cardnum = i + 1
                        self.sols = c[i].sols
                        self.sols2 = c[i].sols2
                        break
    def isEq(self, sol1, sol2, debug = False):
        s1 = sol1.replace('\n', ' ').split(' ')
        s2 = sol2.replace('\n', ' ').split(' ')
        if s1[-1] != s2[-1]: return False
        opf = [[i[1], i[6], i[11]] for i in (s1, s2)]
        for i in opf: i.sort()
        for i in (0, 1): opf[i] = tuple(opf[i])
        af = [(i[4], i[9]) for i in (s1, s2)]
        nf = [[[i[0], i[2]], [i[5], i[7]], [i[10], i[12]]] for i in (s1, s2)]
        for j in (0, 1):
            for i in nf[j]: i.sort()
            for i in (0, 1, 2):
                nf[j][i] = tuple(nf[j][i])
            nf[j].sort()
            nf[j] = tuple(nf[j])
        eq = [[i[j * 5:j * 5 + 3] + [i[j * 5 + 4]] for j in range(3)] for i in (s1, s2)]
        for i in eq:
            for j in i:
                for k in range(len(j)):
                    if j[k].isdigit(): j[k] = int(j[k])
        for i in range(len(eq)):
            for j in range(len(eq[i])):
                eq[i][j] = tuple(eq[i][j])
            eq[i] = tuple(eq[i])
        for i in (0, 1):
            if eq[i][2][0] not in (eq[1 - i][2][0], eq[1 - i][2][2]) or eq[i][2][2] not in (eq[1 - i][2][0], eq[1 - i][2][2]): return False
        if eq[0][2][1] != eq[1][2][1]: return False
        working = True
        for i in (0, 1, 2):
            if eq[0][i][1] != eq[1][i][1] or ((eq[0][i][0] != eq[1][i][0] or eq[0][i][2] != eq[1][i][2]) and (eq[0][i][0] != eq[1][i][2] or eq[0][i][2] != eq[1][i][0])) or eq[1][i][3] != eq[0][i][3]: working = False
        if working: return True
        if opf[0] in (tuple(['×'] * 3), tuple(['+'] * 3)) and opf[1] in (tuple(['×'] * 3), tuple(['+'] * 3)) and opf[0] == opf[1]: return True
        if opf[0] == ('+', '+', '-') and opf[1] == ('+', '+', '-'): return True
        if opf[0] == ('×', '×', '÷') and opf[1] == ('×', '×', '÷'): return True
        if opf[0] == ('+', '-', '-') and opf[1] == ('+', '-', '-'): return True
        if opf[0] == ('-', '-', '-') and opf[1] == ('-', '-', '-'): return True
        if opf[0] == opf[1]: return True
        if (eq[0][0][1], eq[0][1][1]) == ('+', '+') and eq[0][2][1] in ('×', '÷') and (eq[0][0][1], eq[0][1][1]) == ('+', '+') and eq[0][2][1] in ('×', '÷'): return True
        if eq[0][1][1] == '-' and eq[0][2][1] == '-' and eq[1][1][1] == '-' and eq[1][2][1] == '-' and eq[0][1][2] + eq[0][2][2] == eq[1][1][2] + eq[1][2][2] and eq[0][1][0] == eq[1][1][0]: return True
        for i in (0, 1):
            if opf[i] != opf[1 - i] or nf[i] != nf[1 - i]: return False
        if af[0][0] not in af[1] or af[0][1] not in af[1] or af[1][0] not in af[0] or af[1][1] not in af[0]: return False
        return True
    def solutions(self, unique = None):
        if unique == None: unique = self.unique
        if unique: return self.sols2
        else: return self.sols
    def genCard(clear, cardType, rnd = None):
        if type(cardType) != str: ct = card.cardTypes[catdType]
        else: ct = cardType
        if rnd == None: rnd = random.Random()
        rnd.seed()
        if ct.lower()[0] == 'r':
            c = [rnd.choice(range(1, 25)) for i in range(4)]
            c1 = card(c)
            while not c1.cardWorks():
                c = [rnd.choice(range(1, 25)) for i in range(4)]
                c1 = card(c)
            return c1
        elif ct.lower()[0] == 'v':
            c = [rnd.choice(range(1, 25)) for i in range(6)]
            c1 = card(c)
            while not c1.cardWorks(range(1,10)):
                c = [rnd.choice(range(1, 25)) for i in range(6)]
                c1 = card(c)
            return c1
        elif ct.lower()[0] == 'w':
            c = [rnd.choice(range(1, 25)) for i in range(12)]
            c1 = card(c)
            while not c1.cardWorks(range(1,10)):
                c = [rnd.choice(range(1, 25)) for i in range(12)]
                c1 = card(c)
            return c1
        elif ct.lower()[0] == 'q':
            c = [[rnd.choice(range(1, 25)) for i in range(4)] for j in range(4)]
            cc = [card(i) for i in c]
            ccw = [i.cardWorks() for i in cc]
            while not xor(*ccw):
                if ccw[0] or ccw[1] or ccw[2] or ccw[3]:
                    working = []
                    for i in range(4):
                        if ccw[i]: working.append(i)
                    cng = rnd.choice(working) 
                    c[cng] = [rnd.choice(range(1, 25)) for i in range(4)]
                    cc[cng] = card(c[cng])
                    ccw[cng] = cc[cng].cardWorks()
                else:
                    notWorking = []
                    for i in range(4):
                        if not ccw[i]: notWorking.append(i)
                    cng = rnd.choice(notWorking) 
                    c[cng] = [rnd.choice(range(1, 25)) for i in range(4)]
                    cc[cng] = card(c[cng])
                    ccw[cng] = cc[cng].cardWorks()
            rtnn = [i for j in c for i in j]
            return card(rtnn)
    genCard = classmethod(genCard)
    def printFile(self, fileName):
        f1 = file(fileName + '.24crd', 'w')
        f2 = file(fileName + '.24cdt', 'w')
        f3 = file(fileName + '.24cs1', 'w')
        f4 = file(fileName + '.24cs2', 'w')
        f1.write(','.join([str(i) for i in self.numbers]))
        f2.write(self.cardType)
        self.solve()
        pnt1 = ''
        pnt2 = ''
        if self.cardType == 'Regular':
            pnt1 += '\n\n'.join(self.sols)
            pnt2 += '\n\n'.join(self.sols2)
        elif self.cardType == 'Variable':
            for i in range(10):
                pnt1 += ';\n'
                pnt2 += ';\n'
                for j in (0, 1):
                    pnt1 += '\n\n'.join(self.sols[i][j])
                    pnt2 += '\n\n'.join(self.sols2[i][j])
                    if j != 1:
                        pnt1 += ':\n'
                        pnt2 += ':\n'
        elif self.cardType == 'Wheel':
            for i in range(10):
                pnt1 += ';\n'
                pnt2 += ';\n'
                for j in (0, 1, 2, 3):
                    pnt1 += '\n\n'.join(self.sols[i][j])
                    pnt2 += '\n\n'.join(self.sols2[i][j])
                    if j != 3:
                        pnt1 += ':\n'
                        pnt2 += ':\n'
        elif self.cardType == 'Quad':
            pnt1 += str(self.cardNum) + '\n'
            pnt2 += str(self.cardNum) + '\n'
            pnt1 += '\n\n'.join(self.sols)
            pnt2 += '\n\n'.join(self.sols2)
        f3.write(pnt1)
        f4.write(pnt2)
        f1.close()
        f2.close()
        f3.close()
        f4.close()
    def __repr__(self):
        return self.cardType + ';' + ','.join([str(i) for i in self.numbers])
    def printSols(self, unique = None):
        if unique == None: unique = self.unique
        if unique: sols = self.sols2
        else: sols = self.sols
        if self.cardType == 'Regular':
            for i in sols:
                print i
                print ''

###c = card([1,2,3,4])
###c = card([5,3,2,16])
##c = card([7,14,11,8])
##c.solve()
##c.unique = True
##print "for i in c.solutions(): print i + '\\n\\n'"
def ordinal(num):
    if num == 1: return "First"
    elif num == 2: return "Second"
    elif num == 3: return "Third"
    elif num == 4: return "Fourth"
def getInput():
    cls()
    print "Type one of the following:"
    print "sr - solve a regular card        sq - solve a quad card"
    print "sv - solve a variable card       sw - solve a wheel card"
    print "gr - generate a regular card     gq - generate a quad card"
    print "gv - generate a variable card    gw - generate a wheel card"
    print "q - quit"
    print ""
    do = raw_input("What would you like to do? ").lower().strip()
    while do[0] != 'q':
        if do[0] == 's':
            num = []
            if do[1] == 'r':
                for i in range(4):
                    num.append(int(raw_input("Input " + ordinal(i + 1) + " Number: ")))
            elif do[1] == 'v':
                for i in range(2):
                    print "Card " + str(i + 1) + ":\n"
                    for j in range(3):
                        num.append(int(raw_input("Input " + ordinal(j + 1) + " Number: ")))
            elif do[1] == 'w':
                for i in range(4):
                    print "Card " + str(i + 1) + ":\n"
                    for j in range(3):
                        num.append(int(raw_input("Input " + ordinal(j + 1) + " Number: ")))
            elif do[1] == 'q':
                for i in range(4):
                    print "Card " + str(i + 1) + ":\n"
                    for j in range(4):
                        num.append(int(raw_input("Input " + ordinal(j + 1) + " Number: ")))
            c = card(num)
            unique = raw_input("Show only unique solutions? ").lower().strip()[0] in ("t", "y", "1")
            c.solve()
            sols = c.solutions(unique)
            sols = [i.replace('÷', '/').replace('×', '*') for i in self.sols]
            if len(sols) == 0:
                print "No solutions exist."
                tmp = raw_input("Press enter to continue...")
            elif do[1] == 'r':
                for i in sols:
                    print i
                    tmp = raw_input("Press enter to continue...")
                    cls()
            elif do[1] == 'v':
                for i in range(len(sols)):
                    print "Variable: " + str(i + 1) + ':\n'
                    for j in range(len(sols[i])):
                        print ordinal(j + 1) + " Card:\n"
                        for k in sols[i][j]:
                            print k
                            tmp = raw_input("Press enter to continue...")
                            cls()
            elif do[1] == 'w':
                for i in range(len(sols)):
                    print "Variable: " + str(i + 1) + ':\n'
                    for j in range(len(sols[i])):
                        print ordinal(j + 1) + " Card:\n"
                        for k in sols[i][j]:
                            print k
                            tmp = raw_input("Press enter to continue...")
                            cls()
            elif do[1] == 'q':
                print "Working Card: " + str(c.cardnum) + '\n'
                for i in sols:
                    print i
                    tmp = raw_input("Press enter to continue...")
                    cls()
        elif do[0] == 'g':
            c = card.genCard(do[1])
            if do[1] == 'r':
                for i in range(4):
                    print ordinal(i + 1).ljust(6) + " Number: " + str(c.numbers[i])
            elif do[1] == 'v':
                for i in range(2):
                    print ordinal(i + 1) + " Card:\n"
                    for j in range(2):
                        print ordinal(j + 1).ljust(6) + " Number: " + str(c.numbers[i * 3 + j])
            elif do[1] == 'w':
                for i in range(4):
                    print ordinal(i + 1) + " Card:\n"
                    for j in range(3):
                        print ordinal(j + 1).ljust(6) + " Number: " + str(c.numbers[i * 3 + j])
            elif do[1] == 'q':
                for i in range(4):
                    print ordinal(i + 1) + " Card:\n"
                    for j in range(4):
                        print ordinal(j + 1).ljust(6) + " Number: " + str(c.numbers[i * 4 + j])
            tmp = raw_input("Press enter to continue...")
        cls()
        print "Type one of the following:"
        print "sr - solve a regular card        sq - solve a quad card"
        print "sv - solve a variable card       sw - solve a wheel card"
        print "gr - generate a regular card     gq - generate a quad card"
        print "gv - generate a variable card    gw - generate a wheel card"
        print "q - quit"
        print ""
        do = raw_input("What would you like to do? ").lower().strip()

if __name__ == '__main__': getInput()
