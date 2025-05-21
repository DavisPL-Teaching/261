/*
    One of the example questions on the exam.
*/

method F1(x: int) returns (y: int) {
    y := 2 * (x + 1);
}

method F2(x: int) returns (y: int) {
    y := 2 * x + 2;
}

// What will happen when I uncomment the assertions below?
method TestF1F2Equivalent(x: nat) {
    // assert F1(x) == F2(x);

    // var y1 := F1(x);
    // var y2 := F2(x);
    // assert y1 == y2;
}
