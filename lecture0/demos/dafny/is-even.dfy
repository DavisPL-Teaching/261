/*
    The IsEven example that we showed in class, illustrated in Dafny.
*/

method IsEven(x: int) returns (y: bool)
    // Try uncommenting one of the following.
    // ===== Definition of correctness 1 =====
    // (Definition of correctness == Specification)
    // The program should return whether x is even on all inputs
    // requires true
    // ensures y == (x % 2 == 0)
    // ===== Definition of correctness 2 =====
    // The program should return whether x is even on all inputs between 0 and 5
    // requires x >= 0
    // requires x <= 5
    // ensures y == (x % 2 == 0)
{
    if x == 0 {
        return true;
    } else if x == 1 {
        return false;
    } else if x == 2 {
        return true;
    } else if x == 3 {
        return false;
    } else if x == 4 {
        return true;
    } else {
        return false;
    }
}

method Main()
{
    // Run some example calls
    var y2 := IsEven(2);
    print "IsEven(2) = ", y2, "\n";
    var y6 := IsEven(6);
    print "IsEven(6) = ", y6, "\n";
}
