; ModuleID = 'mini-c'
source_filename = "mini-c"

declare i32 @print_int(i32)

define i1 @palindrome(i32 %number) {
entry:
  %result = alloca i1, align 1
  %rmndr = alloca i32, align 4
  %rev = alloca i32, align 4
  %t = alloca i32, align 4
  %number1 = alloca i32, align 4
  store i32 %number, i32* %number1, align 4
  store i32 0, i32* %rev, align 4
  store i1 false, i1* %result, align 1
  %number2 = load i32, i32* %number1, align 4
  store i32 %number2, i32* %t, align 4
  br label %loopcond

loopcond:                                         ; preds = %loopbody, %entry
  %number3 = load i32, i32* %number1, align 4
  %gttmp = icmp ugt i32 %number3, 0
  br i1 %gttmp, label %loopbody, label %loopend

loopbody:                                         ; preds = %loopcond
  %number4 = load i32, i32* %number1, align 4
  %modtmp = srem i32 %number4, 10
  store i32 %modtmp, i32* %rmndr, align 4
  %rev5 = load i32, i32* %rev, align 4
  %multmp = mul i32 %rev5, 10
  %rmndr6 = load i32, i32* %rmndr, align 4
  %addtmp = add i32 %multmp, %rmndr6
  store i32 %addtmp, i32* %rev, align 4
  %number7 = load i32, i32* %number1, align 4
  %divtmp = sdiv i32 %number7, 10
  store i32 %divtmp, i32* %number1, align 4
  br label %loopcond

loopend:                                          ; preds = %loopcond
  %t8 = load i32, i32* %t, align 4
  %rev9 = load i32, i32* %rev, align 4
  %eqtmp = icmp eq i32 %t8, %rev9
  %0 = sitofp i1 %eqtmp to float
  %1 = fptoui float %0 to i1
  br i1 %1, label %then, label %else

then:                                             ; preds = %loopend
  store i1 true, i1* %result, align 1
  br label %ifcont

else:                                             ; preds = %loopend
  store i1 false, i1* %result, align 1
  br label %ifcont

ifcont:                                           ; preds = %else, %then
  %result10 = load i1, i1* %result, align 1
  ret i1 %result10
}
