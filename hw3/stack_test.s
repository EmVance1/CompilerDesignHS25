.text
.globl stack_test_asm

stack_test_asm:
    pushq %rbp
    xor %rax, %rax
    movq %rsp, %rdi
    andq $15, %rdi
    setz %al
    popq %rbp
    retq
