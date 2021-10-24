; ModuleID = 'mini-c'
source_filename = "mini-c"

@test = common global i32 0, align 4
@f = common global float 0.000000e+00, align 4
@b = common global i1 false, align 4

declare i32 @print_int(i32)

define i32 @While(i32 %n) {
entry:
  %result = alloca i32, align 4
  %n1 = alloca i32, align 4
  store i32 %n, i32* %n1, align 4
  store i32 0, i32* %result, align 4
  store i32 12, i32* @test, align 4
  store i32 0, i32* %result, align 4
  %test = load i32, i32* @test, align 4
  %calltmp = call i32 @print_int(i32 %test)
  br label %loophead

loophead:                                         ; preds = %loop, %entry
  %result2 = load i32, i32* %result, align 4
  %conv = sitofp i32 %result2 to float
  %lttmp = fcmp ult float %conv, 1.000000e+01
  %booltmp = uitofp i1 %lttmp to float
  %whilecond = fcmp one float %booltmp, 0.000000e+00
  br i1 %whilecond, label %loop, label %loopend

loop:                                             ; preds = %loophead
  %result3 = load i32, i32* %result, align 4
  %addtmp = add i32 %result3, 1
  store i32 %addtmp, i32* %result, align 4
  br label %loophead

loopend:                                          ; preds = %loophead
  %result4 = load i32, i32* %result, align 4
  ret i32 %result4
}
