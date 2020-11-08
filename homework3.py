
import re
import queue
import time


# In[60]:

def pprint(someMap,title = ""):
    if title != "":
        print("\n",title)
    if type(someMap) == dict:
        for key in someMap:
            print(key," : ")
            if type(someMap[key]) == dict:
                for keyTwo in someMap[key]:
                    print("\t",keyTwo," : ")
                    for val in someMap[key][keyTwo]:
                        print("\t\t",val)
            else:
                for val in someMap[key]:
                     print("\t\t",val)
    else:
        for val in someMap:
            print("\t",val)


# In[61]:


def input_reader(filename):
    file = open(filename,'r')
    nq = file.readline().strip()
    nq = int(nq)
    query_array = []
    for i in range(nq):
        query_array.append(file.readline().strip())
    
    nkb = file.readline().strip()
    nkb = int(nkb)
    kb_array = []
    for i in range(nkb):
        kb_array.append(file.readline().strip())

    return nq,query_array,nkb,kb_array


# In[62]:


def convert_to_cnf(alpha,beta):
    cnf = ""
    predicates = re.split("&", alpha)
    for predicate in predicates:
        if predicate[0] == "~":
            cnf += predicate[1:]+"|"
        else:
            cnf += "~"+predicate+"|"
    cnf = cnf[:-1] #get rid of last |
    cnf += "|" + beta
    return cnf


# In[63]:


def add_clauses(kb_array,clause_hash = {},pred_hash = {},constant_hash = {}):
#     clause_hash = {}    
#     clause_predicate_hash = {}
    clause_list = set()
    
    for pos_clause in kb_array:
        found_match = re.split("=>", pos_clause)
        if len(found_match) == 2: #hohoho its a clause
            alpha = re.sub(r'\s+', '', found_match[0])            
            beta = re.sub(r'\s+', '', found_match[1])
            
            clause = convert_to_cnf(alpha,beta)
            predicates = re.split('\|', clause)
            clause_list.add(clause)
#             print(predicates)
            for pred in predicates:
                pred_title = re.search("^[~A-Z][a-zA-Z1-9]*\(", pred).group()
                pred_title = pred_title[:-1]
                if pred_title not in clause_hash:
                    clause_hash[pred_title] = {}
                if pred not in clause_hash[pred_title]:
                    clause_hash[pred_title][pred] = set()          
                clause_hash[pred_title][pred].add(clause)
            pred_hash,constant_hash,_ = add_predicates(predicates,pred_hash,constant_hash)
            
    return clause_hash,pred_hash,constant_hash,clause_list


# In[64]:


def add_predicates(kb_array,kb_hash = {},constant_hash = {}):
    clause_hash = {}

    for sentence in kb_array:
        whole_match = re.search("^[~A-Z][a-zA-Z1-9]*\([a-zA-Z1-9]*(,[a-zA-Z1-9]*)*\)$", sentence)
        if whole_match:
            predicate_whole = whole_match.group()
            
            predicate_match = re.search("^[~A-Z][a-zA-Z1-9]*\(",predicate_whole)
            predicate = predicate_match.group()[:-1]
            
            argument_match = re.split("[~A-Z][a-zA-Z1-9]*\(|,|\)",predicate_whole)
#             arguments = list(filter(lambda x: (x != "") , argument_match))             
            arguments = tuple(filter(lambda x: (x != "") , argument_match))  
            constants = list(filter(lambda x: ( re.search("^[A-Z][a-zA-Z1-9]*", x) ) , arguments))
            
            for constant in constants:
                if constant not in constant_hash:
                    constant_hash[constant] = set()
                constant_hash[constant].add(predicate_whole)

            
            if predicate not in kb_hash:
                kb_hash[predicate] = set()                
            
            if predicate not in clause_hash:
                clause_hash[predicate] = {}
            if predicate_whole not in clause_hash[predicate]:
                    clause_hash[predicate][predicate_whole] = set()
            
            clause_hash[predicate][predicate_whole].add(predicate_whole)
            kb_hash[predicate].add(arguments)


    
    return kb_hash,constant_hash,clause_hash


# In[79]:


def hash_update(old_hash,new_hash):
    og_hash = {}
    for key in old_hash:
        if key not in og_hash:
            og_hash[key] = {}
        for key2 in old_hash[key]:
            if key2 not in og_hash:
                og_hash[key][key2] = set()
            for val in old_hash[key][key2]:
                og_hash[key][key2].add(val)
    
    for key in new_hash:
        if key in og_hash:
            for key2 in new_hash[key]:
                if key2 in og_hash[key]:
                    for val in new_hash[key][key2]:
                        og_hash[key][key2].add(val)
                else:
                    og_hash[key][key2] = new_hash[key][key2]
        else:
            og_hash[key] = new_hash[key]
    return og_hash


# In[80]:


def get_contradictions(query_array):
    result_list = []
    for query in query_array: 
        if query[0] == "~":
            result_list.append(query[1:])
        else:
            result_list.append("~"+query)
    return result_list


# In[81]:


def invert(pred):
    if pred[0] == "~":
        return pred[1:]
    else:
        return "~"+pred


# In[82]:


def delete_pred_from_clause(pred,clause): 
    #WITH OTHER STATMENTS
    clause = clause.replace("|"+pred+'|', "|")
    clause = clause.replace("|"+pred, "")
    clause = clause.replace(pred+"|", "")
    #SINGLE
    clause = clause.replace(str(pred), "")
    return clause
def unify_clauses(pred,pred_clause,og_clause):
    if pred[0] == "~":
        part1 = delete_pred_from_clause(pred[1:],og_clause)
        part2 = delete_pred_from_clause(pred,pred_clause)
    else:
        part2 = delete_pred_from_clause("~"+pred,og_clause)
        part1 = delete_pred_from_clause(pred,pred_clause)
    if part1 == "":
        new_clause = part2
    elif part2 == "":
        new_clause = part1
    else:
        new_clause = part1+"|"+part2
    
    
#     tautology = check_tautology(new)
    return new_clause,False


# In[83]:


def isConstant(x):
    if x == "|":
        return True
    return re.search("^[A-Z][a-zA-Z1-9]*", x) != None

def add_to_substitution(variable,constant,substitution,both_var = False):
    
    if variable not in substitution:
        substitution[variable] = set()
    
    substitution[variable].add(constant)
        


def sub_oldvar_w_newvar(old_var,new_var,pred):
    pred = pred.replace("("+old_var+")", "("+new_var+")") 
    pred = pred.replace(","+old_var+",", ","+new_var+",")    
    pred = pred.replace("("+old_var+",", "("+new_var+",")    
    pred = pred.replace(","+old_var+")", ","+new_var+")")  
    return pred
def substitute_new_var(old_var,new_var,pred,clauses):
    pred = sub_oldvar_w_newvar(old_var,new_var,pred)  
    new_clauses = set()
    for clause in clauses:
        new_clauses.add(sub_oldvar_w_newvar(old_var,new_var,clause))

    return pred,new_clauses
def standardize(new_pred,new_clauses,org_pred,og_clause):
    
#     stand_pred = ""
#     stand_clause = set()
    
    argument_match_org = re.split("[~A-Z][a-zA-Z1-9]*\(|,|\)",org_pred)
    org_arguments = list(filter(lambda x: (x != "") , argument_match_org))
    
    argument_match_new = re.split("[~A-Z][a-zA-Z1-9]*\(|,|\)",new_pred)
    new_arguments = list(filter(lambda x: (x != "") , argument_match_new))   
    
#     if len(new_arguments) != len(org_arguments):
#         print("ERRRRRROORRRRRR!!!!!!")
    
    argument_match_org = re.split("[~A-Z][a-zA-Z1-9]*\(|,|\)",og_clause)
    og_arguments_clause = list(filter(lambda x: (x != "") , argument_match_org))
    
    new_variables = set( filter( lambda x: not isConstant(x) , og_arguments_clause))
    if new_variables == set():
    #     if org_variables == set():
        return new_pred,new_clauses
    
    clause_arguments_set = set()
    for clause in new_clauses:
        argument_match_clause = re.split("[~A-Z][a-zA-Z1-9]*\(|,|\)",clause)
        clause_arguments = list(filter(lambda x: (x != "") , argument_match_clause))
        clause_arguments_set.update(set(clause_arguments))
        new_variables.update(set( filter( lambda x: not isConstant(x) , clause_arguments)))
    #Only constants in the org pred
    
    
#     print("Org Set",org_variables)    
#     print("New Set",new_variables,"New pred",new_pred)

    
#     for i in range(len(new_arguments)):
# #         if not isConstant(new_arguments[i]) and new_arguments[i] in org_variables:        
#         if not isConstant(new_arguments[i]) :
#             counter = 0
#             variable = new_arguments[i]
# #             while variable in org_variables or variable in new_variables:
#             while variable in new_variables:
#                 counter += 1
#                 variable = new_arguments[i]+str(counter)
#             new_variables.add(variable)
# #             new_variables.remove(new_arguments[i])
#             print("new variable",variable,"old var",new_arguments[i])
#             new_pred,new_clauses =  substitute_new_var(new_arguments[i],variable,new_pred,new_clauses)
    for old_arg in clause_arguments_set:
#         if not isConstant(new_arguments[i]) and new_arguments[i] in org_variables:        
        if not isConstant(old_arg) :
            counter = 0
            variable = old_arg
#             while variable in org_variables or variable in new_variables:
            while variable in new_variables:
                counter += 1
                variable = old_arg+str(counter)
            new_variables.add(variable)
#             new_variables.remove(new_arguments[i])
#             print("new variable",variable,"old var",old_arg)
            new_pred,new_clauses =  substitute_new_var(old_arg,variable,new_pred,new_clauses)
    
#     print("STANDARD",new_pred,new_clauses)
    #ISSUE No.1
    return new_pred,new_clauses


# In[84]:



def perform_substitution(substitution,org_pred,og_query,new_pred,new_clauses):
    old_clauses = new_clauses
    new_clauses = list(old_clauses)
    org_pred_list = []
    og_query_list = []
    new_pred_list= []
    new_clauses_list = []
#     print("BEFROE New Pred ",new_pred," \n Clause",new_clauses,"\n OG",org_pred)
#     more_clauses
    for var in substitution:
        sub = list(substitution[var]) [0]
        org_pred = sub_oldvar_w_newvar(var,sub,org_pred)    
        og_query = sub_oldvar_w_newvar(var,sub,og_query)        
        new_pred = sub_oldvar_w_newvar(var,sub,new_pred)
        for i in range(len(new_clauses)):
            new_clauses[i] = sub_oldvar_w_newvar(var,sub,new_clauses[i])

    new_clauses = set(new_clauses)
    org_pred_list.append(org_pred)
    og_query_list.append(og_query)
    new_pred_list.append(new_pred)
    new_clauses_list.append(new_clauses)
    
    new_clauses = list(old_clauses)
    for var in substitution:
        subs = substitution[var]
        if len(subs) != 1:
            for sub in subs:
                org_pred = sub_oldvar_w_newvar(sub,var,org_pred)    
                og_query = sub_oldvar_w_newvar(sub,var,og_query)        
                new_pred = sub_oldvar_w_newvar(sub,var,new_pred)
                for i in range(len(new_clauses)):
                    new_clauses[i] = sub_oldvar_w_newvar(sub,var,new_clauses[i])
        else:
            sub = list(subs)[0]
            org_pred = sub_oldvar_w_newvar(var,sub,org_pred)    
            og_query = sub_oldvar_w_newvar(var,sub,og_query)        
            new_pred = sub_oldvar_w_newvar(var,sub,new_pred)
            for i in range(len(new_clauses)):
                new_clauses[i] = sub_oldvar_w_newvar(var,sub,new_clauses[i])
    
    new_clauses = set(new_clauses)
    org_pred_list.append(org_pred)
    og_query_list.append(og_query)
    new_pred_list.append(new_pred)
    new_clauses_list.append(new_clauses)
#     print(" AFTREE New Pred ",new_pred," \n SUB Clause",new_clauses,"\n OG",org_pred)
#     print(new_pred_list,new_clauses_list,org_pred_list,og_query_list)
    return new_pred_list,new_clauses_list,org_pred_list,og_query_list
            
def unify(new_pred,new_clauses,org_pred,og_query):
#     print("IN unification",new_pred,org_pred)
    argument_match_org = re.split("[~A-Z][a-zA-Z1-9]*\(|,|\)",org_pred)
    org_arguments = list(filter(lambda x: (x != "") , argument_match_org))
    
    argument_match_new = re.split("[~A-Z][a-zA-Z1-9]*\(|,|\)",new_pred)
    new_arguments = list(filter(lambda x: (x != "") , argument_match_new))   
    
#     if len(new_arguments) != len(org_arguments):
#         print("ERRRRRROORRRRRR!!!!!!")
    
    substitution = {}
    for i in range(len(org_arguments)):
        is_org_constant = isConstant(org_arguments[i])
        is_new_constant = isConstant(new_arguments[i])
        #Unmatching constants
        if is_org_constant and is_new_constant:
            if org_arguments[i] != new_arguments[i]:
                return False,new_pred,new_clauses,org_pred,og_query
        #Variable and Constant
        elif is_org_constant or is_new_constant:
            if is_org_constant:
                add_to_substitution(new_arguments[i],org_arguments[i],substitution)
            else:
                add_to_substitution(org_arguments[i],new_arguments[i],substitution)
        #Varaible and Variable
        else:
            add_to_substitution(new_arguments[i],org_arguments[i],substitution)#             
#             add_to_substitution(org_arguments[i],new_arguments[i],substitution)

         
    new_pred,new_clauses,org_pred,og_query = perform_substitution(substitution,org_pred,og_query,new_pred,new_clauses)
#     print("\nnewpred",new_pred,"new clauses",new_clauses,"org_pred",org_pred,"org_query",og_query,"\nsubstituion",substitution,"endofsub\n")
    return True,new_pred,new_clauses,org_pred,og_query
    
def filter_unifiable(org_pred,og_query,predicates):
    unifiable_preds = {}
    unified_og_query = {}
    for pred in predicates:
        stand_pred,stand_clauses = standardize(pred,predicates[pred],org_pred,og_query)
#         print("STAND PREDICATES",stand_pred,org_pred)
#         print("PRINT CLAUSES",stand_clauses,og_query)
        
        success,key,val,new_ogpred,new_ogquery = unify(stand_pred,stand_clauses,org_pred,og_query)
        if success:
            for i in range(len(new_ogquery)):
    #             print(success,type(key),type(val),type(new_ogpred),type(new_ogquery))
                if key[i] in unifiable_preds:
                    unifiable_preds[key[i]].update(val[i])
                else:
                    unifiable_preds[key[i]] = val[i]
                unified_og_query[new_ogquery[i]] = key[i]
    
#     print("UNIFIED",unified_og_query)
    return unified_og_query,unifiable_preds


# In[85]:


# def resolution_v2(query,clause_hash,depth,Max_depth,query_set):
#     if depth == Max_depth:
#         return True
#     print("Max depth",Max_depth,"cur depth",depth)

# #     print("query",query,"Depth ",depth)
#     og_predicates = query.split("|")
#     if set(og_predicates) in query_set:
#         return True
#     else:
#         query_set.add(set(og_predicates))
        
#     for og_pred in og_predicates:
# #         print("og_pored",og_pred)
#         pred_title = re.search("^[~A-Z][a-zA-Z1-9]*\(", og_pred).group()
#         pred_title = pred_title[:-1]

#         inverse_pred_title = invert(pred_title)
#         if inverse_pred_title not in clause_hash:
#             continue
        
#         predicates = clause_hash[inverse_pred_title]
#         unified_query,unifiable = filter_unifiable(og_pred,query,predicates)
# #         pprint(unifiable,"Possible predicates")

#         for u_query in unified_query:
# #             print("whole query",query)
#             pred = unified_query[u_query]
# #             print("NEW PREDS",unifiable[pred])
#             for clause in unifiable[pred]:
#                     final_clause,tautology = unify_clauses(pred,clause,u_query)
#                     if final_clause == "": #NULL statement
#                         return False
# #                     print("FINAL",final_clause)
# #                     print("\nBEGIN\n",u_query," : ",clause," at Depth",str(depth)+"|","\n",final_clause,"\nEND\n")
#                     #DOES CLAUSE HASH NEED TO BE UPDATED TO PREVENT INFINITE LOOPS
#                     if not resolution_v2(final_clause,clause_hash,depth+1,Max_depth,query_set) and not tautology:
#                         return False
#     return True


# In[86]:


def resolution_v3(query,clause_hash,depth,query_set):
#     if query in query_set:
#         return True
#     else:
#         query_set.add(query)
#     print("query",query,"Depth ",depth)
    frontier = queue.Queue()
    frontier.put(query)
    
    came_from = {}
    came_from[query] = None
    print("Avg time",avg_time)
    while not frontier.empty():
        if time.time() - start > avg_time:
            return True
        query = frontier.get()
#         if query in query_set:
#             continue
#         else:
#             query_set.add(query)
        og_predicates = query.split("|")
        print("prdeicates",og_predicates)

        new_set = frozenset(og_predicates)
        if  new_set in query_set:
#             return True
            continue
        else:
            query_set.add(new_set)
        for og_pred in og_predicates:
            
            # print("og_pored",og_pred)
            if og_pred == '~':
                continue

            pred_title = re.search("^[~A-Z][a-zA-Z1-9]*\(", og_pred).group()
            
            pred_title = pred_title[:-1]

            inverse_pred_title = invert(pred_title)
            if inverse_pred_title not in clause_hash:
                continue

            predicates = clause_hash[inverse_pred_title]
#             print("BeginPrint\nPredicates to branch on query",query," using predicate",og_pred,"\n",predicates,'\nEndPrint\n')
            unified_query,unifiable = filter_unifiable(og_pred,query,predicates)
    #         pprint(unifiable,"Possible predicates")

            for u_query in unified_query:
    #             print("whole query",query)
                pred = unified_query[u_query]
    #             print("NEW PREDS",unifiable[pred])
                for clause in unifiable[pred]:
                        final_clause,tautology = unify_clauses(pred,clause,u_query)
                        if final_clause == "": #NULL statement
                            return False
    #                     print("FINAL",final_clause)
#                         print("\nBEGIN\n",u_query," : ",clause," at Depth",str(frontier.qsize())+"|","\n",final_clause,"using",pred,"\nEND\n")
                        #DOES CLAUSE HASH NEED TO BE UPDATED TO PREVENT INFINITE LOOPS
#                         if not resolution(final_clause,clause_hash,depth+1,query_set) and not tautology:
                        if not tautology :
                        #         and final_clause not in came_from
#                             print("Adding to the frontier ",final_clause,"at",frontier.qsize())
                            if frozenset(final_clause.split("|")) in query_set:
                                continue
                            frontier.put(final_clause)
#                             came_from[final_clause] = query
#                             return False
    return True


# In[87]:


def standardize_kb(kb_list):
    new_list = []
    used_variables = set()
    for clause in kb_list:
        argument_match_org = re.split("[~A-Z][a-zA-Z1-9]*\(|,|\)",clause)
        arguments = list(filter(lambda x: (x != "") , argument_match_org))
        old_variables = set( filter( lambda x: not isConstant(x) and x.isalpha() , arguments))
#         print(clause,old_variables)
        for old_var in old_variables:
            new_var = old_var
            count = 1
            while new_var in used_variables:
                new_var = old_var + str(count)
                count+=1
            used_variables.add(new_var)
            clause = sub_oldvar_w_newvar(old_var,new_var,clause)
        new_list.append(clause)
    return new_list


# In[91]:


if __name__ == '__main__':
    nq,query_array,nkb,kb_array = input_reader("./input.txt")
    nlist = standardize_kb(kb_array)
    kb_array = nlist
    pred_hash,constant_hash,clause_hash = add_predicates(kb_array)  
    if 570/nq > 120:
        avg_time = 120
    else:
        avg_time = 570/nq
    clause_hash,pred_hash,constant_hash,clause_list = add_clauses(kb_array,clause_hash = clause_hash,pred_hash = pred_hash,constant_hash = constant_hash)
    contra_query = get_contradictions(query_array)
    output_text = ""
  
    for query in contra_query:
        start = time.time()
        _,_,cclause_hash = add_predicates([query])
        temp_hash = hash_update(clause_hash,cclause_hash)
        result = resolution_v3(query,temp_hash,0,query_set=set())
        print("RESULT",not result)
        if not result:
            output_text +="TRUE\n"
        else:
            output_text +="FALSE\n"
        if time.time() - start < avg_time:
            addition_time = (avg_time - (time.time() - start))*0.5
            avg_time = avg_time + addition_time
    output_file = open("./output.txt","w")
    print(output_text)
    output_file.write(output_text[:-1])