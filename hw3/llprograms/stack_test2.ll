declare void @stack_test()

define i64 @main(i64 %argc, i8** %argv) {
  %1 = add i64 0, 0
  call void @stack_test()
  ret i64 0
}
