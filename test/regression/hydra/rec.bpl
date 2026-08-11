procedure {:entrypoint} main() {
  call rec(3);
}
procedure rec(n: int) {
  if (n > 0) {
    call rec(n - 1);
  } else {
    assert n >= 0;
  }
}
