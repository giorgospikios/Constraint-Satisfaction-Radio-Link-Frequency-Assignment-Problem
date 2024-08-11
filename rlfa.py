import csp
import sys

def domains_file(filename ,variable_list, variable_domain_map):
    
    file_object = open('rlfap/{}'.format(filename), 'r') #επιστρέφει ένα λεξικό με το αναγνωριστικό της μεταβλητής ως κλειδί 
                                                        #και ως στοιχείο μια λίστα που περιέχει όλες τις πιθανές τιμές που μπορεί να πάρει από τον αντίστοιχο τομέα για αυτή τη μεταβλητή
    file_content = file_object.read()
    file_lines = file_content.splitlines()

    variable_domains={}
    total_values={} # λεξικό με το ID του τομέα ως κλειδί και ως στοιχείο μια λίστα που περιέχει τις τιμές του τομέα

    file_lines_copy = file_lines.copy()
    del file_lines_copy[0]
    for line in file_lines_copy:

        formatted_line = format(line.strip('\n'))
        splitted_line = formatted_line.split(' ')
        splitted_line_copy = splitted_line
        extracted_ids = []
        for sl in splitted_line_copy:
            integer_sl = int(sl)
            extracted_ids.append(integer_sl)

        # for id in extracted_ids[:1]:
        #     used_extracted_ids = extracted_ids.copy()
        #     del used_extracted_ids[0]
        #     del used_extracted_ids[1]
        #     total_values[id] = used_extracted_ids
        for id in extracted_ids[:1]:
            # print("extracted_ids[2:] = ", extracted_ids[2:])
            total_values[id] = extracted_ids[2:]

    for vl in variable_list:
        variable_domains[vl] = total_values[variable_domain_map[vl]]


    file_object.close()
    return variable_domains


#επεξεργασια κειμενου
def variables_file(filename):
    file_object = open('rlfap/{}'.format(filename), 'r') #ανοιγω το αρχείο και παιρνω το αντικείμενο του αρχείου
    file_content = file_object.read() #Ανάγνωση ολόκληρου του περιεχομένου του αρχείου σε μία συμβολοσειρά
    file_lines = file_content.splitlines() # χωριζω το περιεχόμενο του αρχείου σε γραμμές
    variable_ids = [] #Αρχικοποίηση μιας κενής λίστας για την αποθήκευση των μεταβλητών
    variable_domain = {} # αρκικοποιω κενο map για την αποθήκευση ζευγών μεταβλητών-περιοχών

    file_lines_copy = file_lines.copy() #αντιγραφω τα περιεχομενα του file_lines
    del file_lines_copy[0] #και διαγραφω το πρωτο περιεχομενο που ειναι η επικεφαλιδα για να γινει η επαναληψη
    for line in file_lines_copy:  # Επανάληψη των γραμμών του αρχείου ξεκινώντας από τη δεύτερη γραμμή

        formatted_line = format(line.strip('\n')) #αφαιρω τους χαρακτηρες νεας γραμμης
        variable_id, domain_id = formatted_line.split(' ') 
        
        variable_id = int(variable_id)
        variable_ids.append(variable_id)

        domain_id = int(domain_id)
        variable_domain[variable_id] = domain_id

    file_object.close() #κλεισιμο αντικειμενικου αρχειου

    # Επιστρέφει τη λίστα με τα αναγνωριστικά μεταβλητών και το λεξικό με τα ζεύγη μεταβλητών-τομέα
    return variable_ids, variable_domain


def ctrfile(filename):
    
    file_object = open('rlfap/{}'.format(filename), 'r')#περιορισμοί: ένα ζεύγος μεταβλητών, καθώς η πλειάδα είναι το κλειδί και το στοιχείο είναι μια πλειάδα με "k value" και ο αντίπαλος
                                                        #neighbors : το αναγνωριστικό της μεταβλητής είναι το κλειδί 
                                                        #και το στοιχείο είναι μια λίστα που περιέχει όλους τους γείτονες της αντίστοιχης μεταβλητής
    file_content = file_object.read()
    file_lines = file_content.splitlines()

    constraints_map = {}
    neighbors_map = {}

    file_lines_copy = file_lines.copy()
    del file_lines_copy[0]
    for line in file_lines_copy:

        formatted_line = format(line.strip('\n'))
        x, y, k, z = formatted_line.split(' ')
    
        x = int(x)
        y = int(y)
        z = int(z)

        xy_tuple = (x, y)
        yx_tuple = (y, x)
        zk_tuple = (z, k)
        constraints_map[xy_tuple] = zk_tuple
        constraints_map[yx_tuple] = zk_tuple

        if x not in neighbors_map:
            neighbors_map[x] = []
            neighbors_map[x].append(y)
        else:
            neighbors_map[x].append(y)

        if y not in neighbors_map:
            neighbors_map[y] = []
            neighbors_map[y].append(x)
        else:
            neighbors_map[y].append(x)

    file_object.close()
    return constraints_map ,neighbors_map





def check(A, a, B, b):
    
    if (A, B) in constraints: # έλεγχος αν ισχύουν οι περιορισμοί μεταξύ 2 μεταβλητών A και B για τις αντίστοιχες τιμές a,b

        k = constraints[(A, B)][0]
        if constraints[(A, B)][1] == '=':
            return (abs(a-b) == k)
        else:
            return (abs(a-b) > k)
        
    elif (B, A) in constraints:

        k = constraints[(B, A)][0]
        if constraints[(B, A)][1] == '=':
            return (abs(a-b) == k)
        else:
            return (abs(a-b) > k)
            



occurance = sys.argv[1]
variable_name = "var" + occurance + ".txt"
domain_name = "dom" + occurance + ".txt"
ctrname = "ctr" + occurance + ".txt"

variables, variables_domain = variables_file(variable_name)
domains = domains_file(domain_name, variables, variables_domain)
constraints, neighbors = ctrfile(ctrname)


algo = sys.argv[2]
data_objects = csp.CSP(variables, domains, neighbors, check, constraints)


if algo == "fc-cbj":
    print("FC-CBJ algorithm - Dom/wdeg heuristic")
    res = csp.cbj_search(data_objects,select_unassigned_variable=csp.domdeg,order_domain_values=csp.lcv,inference=csp.forward_checking)
    print("result:")
    print(res[0])
    print("\nVisited nodes: %d " % data_objects.nassigns)
    print("\nChecks: %d" % res[1])

if algo == "fc": 
    print("FC algorithm - Dom/wdeg heuristic")
    res = csp.backtracking_search(data_objects, select_unassigned_variable = csp.domdeg, order_domain_values = csp.lcv, inference = csp.forward_checking)
    print("result:")
    print(res[0])
    print("\nVisited nodes: %d " % data_objects.nassigns)
    print("\nChecks: %d" % res[1])

if algo == "min-con":
    print("Min conflicts")
    res = csp.min_conflicts(data_objects)
    print("result:")
    print(res[0])
    print("\nVisited nodes: %d " % data_objects.nassigns)
    print("\nChecks: %d" % res[1])


if algo == "mac":
    print("MAC Algorithm - Dom/wdeg heuristic")
    res = csp.backtracking_search(data_objects, select_unassigned_variable = csp.domdeg, order_domain_values = csp.lcv, inference = csp.mac)
    print("result:")
    print(res[0])
    print("\nVisited nodes: %d " % data_objects.nassigns)
    print("\nChecks: %d" % res[1])