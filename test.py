from solver import (
    check_stanford_master_foundamental_requirements,
    check_stanford_master_breadth_requirements,   
    check_stanford_master_implementation_requirements,
    check_stanford_master_depth_requirements,
    check_stanford_master_elective_requirements,
    check_stanford_master_additional_requirements   
)


def test_foundamental_requrements():
    course_choices = {
        "cs109": [False, 0],
        "ee178": [False, 0],
        "stat116": [False, 4],
        "cme106": [False, 0],
        "cs103": [True, 4],
        "cs161": [True, 4],
        "cs107": [True, 4],
        "cs107e": [False, 0],
        "cs110": [False, 0],
        "cs111": [True, 3],
        "msande220": [False, 0],
    }

    sat_course_choices = {
        "cs109": [True, 3],
        "ee178": [True, 3],
        "stat116": [True, 3],
        "cme106": [True, 3],
        "cs103": [True, 3],
        "cs161": [True, 3],
        "cs107": [True, 3],
        "cs107e": [True, 3],
        "cs110": [True, 3],
        "cs111": [True, 3],
        "msande220": [True, 4],
    }
    print(check_stanford_master_foundamental_requirements(course_choices))
    print(check_stanford_master_foundamental_requirements(sat_course_choices))


#initially manually written test cases: we can try LLM to find better corner cases 
def test_breadth_requrements():
    unsat_course_choices = {
         "cs154": [False, 0],
         "cs140": [True, 3],
         "history244f": [True, 3],
         "cs348a": [True, 3],

    }

    sat_course_choices = {
         "cs154": [True, 4],
        "cs248a": [True, 3],
         "cs140": [True, 4],
         "history244f": [True, 3],
         "cs348a": [True, 4],
    }
    print(check_stanford_master_breadth_requirements(unsat_course_choices))
    print(check_stanford_master_breadth_requirements(sat_course_choices))

def test_implementation_requrements():
    unsat_course_choices = {
    "history244f": [True, 3],
    "cs140": [True, 0],
    "cs140e": [False, 0],
    "cs143": [False, 0],
    "cs144": [False, 0],
    "cs145": [False, 0],
    "cs148": [False, 0],
    "cs151": [False, 0],
    "cs190": [False, 0],
    "cs210b": [False, 0],
    "cs212": [False, 0],
    "cs221": [True, 0],
    "cs227b": [False, 0],
    "cs231n": [False, 0],
    "cs243": [False, 0],
    "cs248": [False, 0],
    "cs248a": [True, 0],
    "cs341": [False, 0]
        

    }

    sat_course_choices = {
    "cs140": [True, 3],
    }
    print(check_stanford_master_implementation_requirements(unsat_course_choices))
    print(check_stanford_master_implementation_requirements(sat_course_choices))

def test_depth_requrements():

    unsat_course_choices = {'cs221': [True, 3], 'cs223a': [True, 3], 'cs224n': [True, 3], 'cs224s': [True, 3], 'cs224u': [False, 0], 'cs224v': [False, 0], 'cs224w': [False, 0], 'cs228': [False, 0], 'cs229': [False, 0], 'cs231a': [False, 0],
                    'cs231n': [False, 0], 'cs234': [False, 0], 'cs237a': [False, 0], 'cs237b': [False, 0], 'cs238': [False, 0], 'cs205l': [False, 0], 'cs224r': [False, 0], 'cs225a': [False, 0], 'cs227b': [False, 0], 'cs229m': [False, 0],
                    'cs230': [False, 0], 'cs233': [False, 0], 'cs235': [False, 0], 'cs236': [False, 0], 'cs239': [False, 0], 'cs246': [False, 0], 'cs257': [False, 0], 'cs270': [False, 0], 'cs271': [False, 0], 'cs273a': [False, 0],
                    'cs273b': [False, 0], 'cs274': [False, 0], 'cs275': [False, 0], 'cs279': [False, 0], 'cs281': [False, 0], 'cs322': [False, 0], 'cs324': [False, 0], 'cs325b': [False, 0], 'cs326': [False, 0], 'cs327a': [False, 0],
                    'cs329_any_suffix': [False, 0], 'cs330': [False, 0], 'cs331b': [False, 0], 'cs332': [False, 0], 'cs333': [False, 0], 'cs345': [False, 0], 'cs348n': [False, 0], 'cs361': [False, 0], 'cs368': [False, 0], 'cs371': [False, 0],
                    'cs375': [False, 0], 'cs377_any_suffix': [False, 0], 'cs379_any_suffix': [False, 0], 'cs398': [False, 0], 'cs399': [False, 0], 'cs428a': [False, 0], 'cs428b': [False, 0], 'cs432': [False, 0], 'ee263': [False, 0],
                    'ee276': [False, 0], 'ee278': [False, 0], 'ee364a': [False, 0], 'ee364b': [False, 0], 'ee377': [False, 0], 'ee378b': [False, 0], 'engr205': [False, 0], 'engr209a': [False, 0], 'msande226': [False, 0], 'msande252': [False, 0],
                    'psych209': [False, 0], 'stats202': [False, 0], 'stats315a': [False, 0], 'stats315b': [False, 0]}
    print(check_stanford_master_depth_requirements(unsat_course_choices))
    
    # Example course choices that satisfy the depth requirement
    sat_course_choices = {
    "cs221": [True, 3],
    "cs223a": [True, 3],
    "cs224n": [True, 3],
    "cs228": [True, 3],
    "cs231a": [True, 3],
    "cs224s": [True, 3],
    "cs224u": [True, 3],
    "cs224v": [True, 3],
    "cs224w": [True, 3],
    "cs231n": [True, 3],
    "cs234": [True, 3],
    "cs237a": [True, 3],
    "cs237b": [True, 3],
    "cs238": [True, 3],
    "cs205l": [True, 3],
    "cs224r": [True, 3],
    "cs225a": [True, 3],
    "cs227b": [True, 3],
    "cs229m": [True, 3],
    "cs230": [True, 3],
    "cs233": [True, 3],
    "cs235": [True, 3],
    "cs236": [True, 3],
    "cs239": [True, 3],
    "cs246": [True, 3],
    "cs257": [True, 3],
    "cs270": [True, 3],
    "cs271": [True, 3],
    "cs273a": [True, 3],
    "cs273b": [True, 3],
    "cs274": [True, 3],
    "cs275": [True, 3],
    "cs279": [True, 3],
    "cs281": [True, 3],
    "cs322": [True, 3],
    "cs324": [True, 3],
    "cs325b": [True, 3],
    "cs326": [True, 3],
    "cs327a": [True, 3],
    "cs329": [True, 3],
    "cs330": [True, 3],
    "cs331b": [True, 3],
    "cs332": [True, 3],
    "cs333": [True, 3],
    "cs345": [True, 3],
    "cs348n": [True, 3],
    "cs361": [True, 3],
    "cs368": [True, 3],
    "cs371": [True, 3],
    "cs375": [True, 3],
    "cs377": [True, 3],
    "cs379": [True, 3],
    "cs398": [True, 3],
    "cs399": [True, 3],
    "cs428a": [True, 3],
    "cs428b": [True, 3],
    "cs432": [True, 3],
    "ee263": [True, 3],
    "ee276": [True, 3],
    "ee278": [True, 3],
    "ee364a": [True, 3],
    "ee364b": [True, 3],
    "ee377": [True, 3],
    "ee378b": [True, 3],
    "engr205": [True, 3],
    "engr209a": [True, 3],
    "msande226": [True, 3],
    "msande252": [True, 3],
    "psych209": [True, 3],
    "stats202": [True, 3],
    "stats315a": [True, 3],
    "stats315b": [True, 3]
    }

    # Call the function to check depth requirements
    print(check_stanford_master_depth_requirements(sat_course_choices))

def test_elective_requirements():
    unsat_seminar_choices = {
       "seminar1": [True, 3],
       "seminar2": [True, 1],
       "seminar3": [True, 2],
    }
    unsat_elective = {
    "cs432": [True, 3],
    "cs129": [True, 3],
    "cs229": [True, 3],
    "ee278": [True, 3],
    "ee364a": [True, 3],
    "ee364b": [True, 3],
    "ee377": [True, 3],
        
    }
    sat_seminar_choices = {
       "seminar1": [True, 1],
       "seminar2": [True, 1],
       "seminar3": [True, 1],
    }
    print(check_stanford_master_elective_requirements(unsat_seminar_choices, unsat_elective))
    print(check_stanford_master_elective_requirements(sat_seminar_choices, unsat_elective))

def test_additional_requirements():
    unsat_course_choices = {
        "cs210": [True, 3, "A"],
        "cs200": [True, 1, "B"],
        "cs500": [True, 1, "C"],
        
        
    }
    print(check_stanford_master_additional_requirements(unsat_course_choices))
    
if __name__ == "__main__":
    '''
    test_foundamental_requrements()
    test_breadth_requrements()
    test_implementation_requrements()
    test_depth_requrements()
    test_elective_requirements()
    '''
    test_additional_requirements()