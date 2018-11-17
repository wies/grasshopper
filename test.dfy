

method test(a: array<int>)
  requires a != null && exists i: int :: 0 <= i < a.Length && a[i] == 0
{
}

method foo(a: array<int>)
  requires a != null && forall i: int :: 0 <= i < a.Length ==> a[i] == 0
{
}