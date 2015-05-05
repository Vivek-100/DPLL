from itertools import product
import itertools
import copy
import sys

def CNF_satisfiability(expr):
    """
    Main function called to check the CNF satisfiablility. 
    Call dpll function to get the satisfiablitity
    """
    end_result = []
    temp_result = []
    i=0
    con_list = eval(expr)
    clauses = find_clauses(con_list)
    symbols = find_symbols(clauses)
    clause, result = dpll(clauses, symbols)
    while(len(end_result) == 0 or i==0):
        if(clause == clauses and len(result) == 0):
            symbol_p = symbols[i]
            symbol_n = ["not", symbols[i]]
            i=i+1
            clause1=copy.copy(clauses)
            clause1.append(symbol_p)
            clause1_p, result1_p = dpll(clause1, symbols)
            if(len(clause1_p) == 0):
                temp_result.insert(0, "true")
                temp_result.extend(result1_p)
                end_result=temp_result
            elif(isinstance(clause1_p, list)):
                for item in clause1_p:
                    if not item:
                       con_list1 = eval(expr)
                       clause2 = find_clauses(con_list1)
                       clause2.append(symbol_n)
                       clause1_n, result1_n = dpll(clause2, symbols)
                       if(len(clause1_n) == 0):
                            temp_result.insert(0, "true")
                            temp_result.extend(result1_n)
                            end_result=temp_result
                       elif(isinstance(clause1_n, list)):
                            for item in clause1_n:
                                if not item:
                                   temp_result.insert(0, "false")
                                   end_result=temp_result
                                   break
        else:
            i=i+1
            if(len(clause) == 0):
                temp_result.insert(0, "true")
                temp_result.extend(result)
                end_result=temp_result
            elif(isinstance(clause, list)):
                for item in clause:
                    if not item:
                       temp_result.insert(0, "false")
                       end_result=temp_result
                       break

    return end_result
    #"""write result on the file"""
    #file = open("CNF_satisfiability.txt", "a+")
    #result_str=str(end_result)
    #file.write(result_str+"\n")

    #file.close()
    
def dpll(clauses, symbols):
    """
    Call find pure symbol and unit propogation functions recursively 
    """
    final_result = []
    clause_after_pure_symbols, result_ps = find_pure_symbol(symbols,clauses)
    final_result.extend(result_ps)
    while(len(result_ps) > 0):
        result_ps = []
        symbols = find_symbols(clause_after_pure_symbols)
        if(len(symbols) > 0):
            clause_after_pure_symbols, result_ps = find_pure_symbol(symbols,clause_after_pure_symbols)
            final_result.extend(result_ps)
    final_clause =copy.copy(clause_after_pure_symbols)
    
    symbols = find_symbols(clause_after_pure_symbols)
    if(len(symbols) > 0):
        clause_after_unit_propagation, result_up = unit_propagatation(symbols, clause_after_pure_symbols)
        final_result.extend(result_up)
        while(len(result_up) > 0):
            result_up = []
            symbols = find_symbols(clause_after_unit_propagation)
            if(len(symbols) > 0):
               clause_after_unit_propagation, result_up = unit_propagatation(symbols,clause_after_unit_propagation)
               final_result.extend(result_up)

        final_clause=copy.copy(clause_after_unit_propagation)
        
    return final_clause, final_result

def find_clauses(exp):
      """
      Function to find clauses in the CNF and change it into set form
      """
      clauses=[]
      if(exp[0]=="and"):
          temp=exp
          temp.pop(0)
          for item in temp:
              if(item[0] == "or"):
                  temp2=item
                  temp2.pop(0)
                  clauses.append(temp2)
              else:
                clauses.append(item)
      elif(exp[0]=="or"):
          temp=exp
          temp.pop(0)
          clauses.append(temp)
      else:
          clauses.append(exp)
      return clauses

def find_symbols(clause):
     """
     Function to find symbols/literals in the clauses/sets
     """
     symbols=[]
     for item in clause:
         if(isinstance(item, list)):
             for insideitem in item:
                if((len(insideitem)==1)  and (insideitem not in symbols) and (insideitem.isupper())):
                    symbols.append(insideitem)
                elif((len(insideitem)==2) and (insideitem[1] not in symbols) and (insideitem[1].isupper())):
                    symbols.append(insideitem[1])
         elif((len(item)==1) and (item not in symbols) and (item.isupper())):
             symbols.append(item)

     return symbols

def find_pure_symbol(symbols, clauses):
   """
   Function to pure symbols/literals in the clauses/sets
   Pure means the symbols which apperared only positive or negative in the set
   """
   temp_sym= [];
   pure_symbol=[]   
   temp = []
   model = []
   result_clauses = []
   for item in symbols:
        pure_positive=0
        pure_negative=0
        for i, clause in enumerate(clauses):
            if(isinstance(clause, list)):
               if(len(clause) == 2 and clause[0] == "not"):
                   if(item == clause[1]):
                    pure_negative = pure_negative + 1
               else:
                   for insideitem in clause:
                        if((len(insideitem)==1) and (item == insideitem)):
                            pure_positive = pure_positive + 1
                        elif((len(insideitem)==2) and (item == insideitem[1])):
                            pure_negative = pure_negative + 1
            elif(item == clause):
                 pure_positive = pure_positive + 1

        if(pure_positive==0 and pure_negative > 0):
                temp_sym=[item + "=false"]
                model.extend(temp_sym)
                neg_item = ["not", item]
                pure_symbol.append(neg_item)
        elif(pure_positive > 0 and pure_negative == 0):
                temp_sym=[item + "=true"]
                model.extend(temp_sym)
                pure_symbol.append(item)
   
   for each_pure_symbol in pure_symbol:
         for i,clause in enumerate(clauses):
             if(clause != each_pure_symbol):
                if str(each_pure_symbol) in clause:
                    for i2,insideclause in enumerate(clause):
                        if(each_pure_symbol == insideclause):
                            temp.append(clause)
             elif(clause == each_pure_symbol):
                 temp.append(clause)

   for each_pure_symbol in pure_symbol:
       if(len(each_pure_symbol)>1):
         for i,clause in enumerate(clauses):
             if(clause != each_pure_symbol):
                #if str(each_pure_symbol) in clause:
                    for i2,insideclause in enumerate(clause):
                        if(each_pure_symbol == insideclause):
                            temp.append(clause)
             elif(clause == each_pure_symbol):
                 temp.append(clause)

   result_clauses = [item for item in clauses if item not in temp]

   return result_clauses, model

def unit_propagatation(symbols,clauses):
   """
   Function to find unit clauses and perform unit propagation
   """
   temp_clause=[];
   unit_clause=[] 
   temp = []
   model = []
   temp_result = []
   result_clauses = []

   for item in symbols:
        neg_item = ["not", item]
        for clause in clauses:
            if(isinstance(clause, list)):
                if((len(clause)==2) and (item == clause[1]) and (clause[0] == "not") and (clause not in unit_clause) and (clause[1] not in unit_clause)):
                     temp_clause = clause
                     unit_clause.append(temp_clause)
                     temp_result = [str(clause[1]) + "=false"]
                     model.extend(temp_result)
                elif((len(clause)==1) and (isinstance(clause[0], list))):
                    if((item == clause[0][1]) and (clause[0][0] == "not") and (clause[0] not in unit_clause) and (clause[0][1] not in unit_clause)):
                         temp_clause = clause
                         unit_clause.append(temp_clause)
                         temp_result = [str(clause[0][1]) + "=false"]
                         model.extend(temp_result)
                elif((len(clause)==1) and item == clause[0] and (item not in unit_clause) and (neg_item not in unit_clause)):
                     temp_clause = item
                     unit_clause.append(temp_clause)
                     temp_result = [str(temp_clause) + "=true"]
                     model.extend(temp_result)
            elif((len(clause)==1) and item == clause and (item not in unit_clause) and (neg_item not in unit_clause)):
                temp_clause = item
                unit_clause.append(temp_clause)
                temp_result = [str(temp_clause) + "=true"]
                model.extend(temp_result)

   for each_unit_clause in unit_clause:
         for i,clause in enumerate(clauses):
             if(clause != each_unit_clause):
                if (each_unit_clause) in list(clause):
                    for i2,insideclause in enumerate(clause):
                        if((each_unit_clause == insideclause) and (clause[0] != "not")):
                            temp.append(clause)
             elif((clause == each_unit_clause)):
                 temp.append(clause)

   for each_unit_clause in unit_clause:
         length = len(each_unit_clause)
         if(length == 1):
             neg_each_unit_clause = ["not", each_unit_clause] 
         elif(length == 2):
             neg_each_unit_clause = each_unit_clause[1]
         for i,clause in enumerate(clauses):
             if(neg_each_unit_clause==clause):
                         clauses[i] =[]
             else:
                 for j,insideclause in enumerate(clause):
                     if(neg_each_unit_clause==insideclause):
                         del clauses[i][j]

   result_clauses = [item for item in clauses if item not in temp]
   return result_clauses, model


result = CNF_satisfiability('["and", ["or", ["not", "P"], "P"], ["or", "Q", "P", ["not", "P"]], ["or", ["not", "P"], ["not", "Q"], "P"], ["or", "Q", ["not", "Q"], "P", ["not", "P"]], ["or", ["not", "P"], ["not", "Q"], "Q"], ["or", "Q", "P", ["not", "Q"]], ["or", "Q", ["not", "Q"]]]')
print result
#read file  
#inputFile = open(sys.argv[2])

#conf=0
#line_number=0
#final_list=[]
#for line in inputFile:
#    if conf==0:
#        spl = line.strip().split(' ')
#        line_number=int(spl[0])
#        file = open("CNF_satisfiability.txt", "w")
#        file.close()
#        conf=1
#    else:
#        CNF_satisfiability(line)
        
#inputFile.close()  
