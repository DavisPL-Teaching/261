"""
The IsEven example that we showed in class, illustrated in Python.
"""

def is_even(x):
    if x == 0:
        return True
    elif x == 1:
        return False
    elif x == 2:
        return True
    elif x == 3:
        return False
    elif x == 4:
        return True
    else:
        return False

if __name__ == "__main__":
    # Run some example calls
    print("is_even(2) = ", is_even(2))
    print("is_even(6) = ", is_even(6))
