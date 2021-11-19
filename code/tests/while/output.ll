; ModuleID = 'mini-c'
source_filename = "mini-c"

@test = global i32 0
@f = global float 0.000000e+00
@b = global i1 false

declare i32 @print_int(i32)

define i32 @While(i32 %n) {
entry:
  %result = alloca i32, align 4
  %n1 = alloca i32, align 4
  store i32 %n, i32* %n1, align 4
  store i32 12, i32* @test, align 4
  store i32 0, i32* %result, align 4
  %0 = load i32, i32* @test, align 4
  %calltmp = call i32 @print_int(i32 %0)
  br label %loopcond

loopcond:                                         ; preds = %loopbody, %entry
  %result2 = load i32, i32* %result, align 4
  %lttmp = icmp ult i32 %result2, 10
  br i1 %lttmp, label %loopbody, label %loopend

loopbody:                                         ; preds = %loopcond
  %result3 = load i32, i32* %result, align 4
  %addtmp = add i32 %result3, 1
  store i32 %addtmp, i32* %result, align 4
  br label %loopcond

loopend:                                          ; preds = %loopcond
  %result4 = load i32, i32* %result, align 4
  ret i32 %result4
}
