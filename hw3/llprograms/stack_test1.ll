declare void @stack_test()

define i64 @main(i64 %argc, i8** %argv) {
  call void @stack_test()
  ret i64 0
}
