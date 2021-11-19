; ModuleID = 'mini-c'
source_filename = "mini-c"

define i32 @factorial(i32 %n) {
entry:
  %factorial = alloca i32, align 4
  %i = alloca i32, align 4
  %n1 = alloca i32, align 4
  store i32 %n, i32* %n1, align 4
  store i32 1, i32* %factorial, align 4
  store i32 1, i32* %i, align 4
  br label %loopcond

loopcond:                                         ; preds = %loopbody, %entry
  %i2 = load i32, i32* %i, align 4
  %n3 = load i32, i32* %n1, align 4
  %letmp = icmp ule i32 %i2, %n3
  br i1 %letmp, label %loopbody, label %loopend

loopbody:                                         ; preds = %loopcond
  %factorial4 = load i32, i32* %factorial, align 4
  %i5 = load i32, i32* %i, align 4
  %multmp = mul i32 %factorial4, %i5
  store i32 %multmp, i32* %factorial, align 4
  %i6 = load i32, i32* %i, align 4
  %addtmp = add i32 %i6, 1
  store i32 %addtmp, i32* %i, align 4
  br label %loopcond

loopend:                                          ; preds = %loopcond
  %factorial7 = load i32, i32* %factorial, align 4
  ret i32 %factorial7
}
