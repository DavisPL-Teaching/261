/*
Lecture 2, Part 4:
Loop invariants: answer key
*/

method MinList(a: array<int>) returns (result: int)
// Precondition: array is nonempty
requires a.Length > 0
// Postcondition: for all i between 0 and the length, the result should be <= a[i]
// and, there exists an i between 0 and the length, such that the result is == a[i].
ensures forall i :: 0 <= i < a.Length ==> result <= a[i]
ensures exists i :: 0 <= i < a.Length && result == a[i]
{
    var min := a[0];
    // invariant should be true here
    for i := 0 to a.Length
    invariant forall j :: 0 <= j < i ==> min <= a[j]
    invariant 0 <= i <= a.Length // implicitly added for for loops - so not technically needed.
    // Option 1:
    invariant i == 0 ==> min == a[0]
    invariant i >= 1 ==> exists j :: 0 <= j < i && min == a[j]
    // Option 2:
    // invariant exists j :: 0 <= j < a.Length && min == a[j]
    {
        if a[i] < min {
            min := a[i];
        }

        // implicit: at the end of each loop, we do i := i + 1

        // invariant should be true here
        // what is true about the array and the variables min, i at this point in the program?
        // min <= a[0]
        // min <= a[0], a[1], ..., a[i-1]
        // i is between 0 and a.Length -- 0 <= i < a.Length
        // min is an element of the array that we've looked at so far: min == a[0], a[1], ..., a[i-1].
    }
    return min;
}

method ArgMinList(a: array<int>) returns (result: int)
requires a.Length > 0
// What to do about ties?
// In the case of ties: return the first index.
ensures 0 <= result < a.Length
ensures forall i :: 0 <= i < a.Length ==> a[result] <= a[i]
ensures forall i :: 0 <= i < result ==> a[result] < a[i]
{
    var min := a[0];
    var min_index := 0;
    for i := 1 to a.Length
    invariant 0 <= min_index < i
    // proof also goes through with the weaker: 0 <= min_index < a.Length.
    invariant min == a[min_index]
    invariant forall j :: 0 <= j < min_index ==> min < a[j]
    invariant forall j :: 0 <= j < i ==> min <= a[j]
    {
        if a[i] < min {
            min := a[i];
            min_index := i;
        }
    }
    result := min_index;
}

method TestMinList() {
    var a0 := new int[][1]; // new keyword: allocates an array on the heap
    var y0 := MinList(a0);
    assert y0 == 1;
    var a1 := new int[][1, 0, 1];
    var y1 := MinList(a1);
    // Helping Dafny out...
    // assert forall i :: 0 <= i < a1.Length ==> y1 <= a1[i];
    // assert exists i :: 0 <= i < a1.Length && y1 == a1[i];
    // assert a1.Length == 3;
    // assert forall i :: 0 <= i < 3 ==> y1 <= a1[i];
    // assert exists i :: 0 <= i < 3 && y1 == a1[i];
    // assert y1 <= a1[0];
    assert y1 <= a1[1];
    // assert y1 <= a1[2];
    // assert y1 <= 0;

    assert y1 == 0;
    // var a2 := new int[][5, 4, 3, 2, 1];
    // var y2 := MinList(a2);
    // assert ...
}
