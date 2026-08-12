// Branch 1 grows the DAG enough to trigger an initial split. In its avoid
// child, branches 2 and 3 merge their mutually-exclusive shared calls; branch
// 4 then grows the DAG again, so the published sibling must replay that merge.
var g: int;

procedure {:entrypoint} main() {
  g := 0;
  if (*) {
    call wrap1();
  } else {
    if (*) {
      call shared();
    } else {
      if (*) {
        call shared();
      } else {
        call wrap4();
      }
    }
  }
}

procedure wrap1() {
  call shared();
}

procedure wrap4() {
  call shared();
}

procedure shared() {
  assert g == 0;
}
