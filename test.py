from solver import (
    check_stanford_master_foundamental_requirements,
    check_stanford_master_breadth_requirements    
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
    course_choices = {
         "cs154": [False, 0],
         "cs140": [True, 3],
         "history244f": [True, 3],
         "cs348a": [True, 3],

    }

    sat_course_choices = {
         "cs154": [True, 4],
         "cs140": [True, 4],
         "history244f": [True, 3],
         "cs348a": [True, 4],


    }
    print(check_stanford_master_breadth_requirements(course_choices))
    print(check_stanford_master_breadth_requirements(sat_course_choices))

if __name__ == "__main__":
    test_foundamental_requrements()
    test_breadth_requrements()