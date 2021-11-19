; ModuleID = 'mini-c'
source_filename = "mini-c"

declare i32 @print_int(i32)

declare float @print_float(float)

define float @unary(i32 %n, float %m) {
entry:
  %sum = alloca float, align 4
  %result = alloca float, align 4
  %m2 = alloca float, align 4
  %n1 = alloca i32, align 4
  store i32 %n, i32* %n1, align 4
  store float %m, float* %m2, align 4
  store float 0.000000e+00, float* %sum, align 4
  %n3 = load i32, i32* %n1, align 4
  %m4 = load float, float* %m2, align 4
  %0 = sitofp i32 %n3 to float
  %addtmp = fadd float %0, %m4
  store float %addtmp, float* %result, align 4
  %result5 = load float, float* %result, align 4
  %calltmp = call float @print_float(float %result5)
  %sum6 = load float, float* %sum, align 4
  %result7 = load float, float* %result, align 4
  %addtmp8 = fadd float %sum6, %result7
  store float %addtmp8, float* %sum, align 4
  %n9 = load i32, i32* %n1, align 4
  %m10 = load float, float* %m2, align 4
  %fnegtmp = fneg float %m10
  %1 = sitofp i32 %n9 to float
  %addtmp11 = fadd float %1, %fnegtmp
  store float %addtmp11, float* %result, align 4
  %result12 = load float, float* %result, align 4
  %calltmp13 = call float @print_float(float %result12)
  %sum14 = load float, float* %sum, align 4
  %result15 = load float, float* %result, align 4
  %addtmp16 = fadd float %sum14, %result15
  store float %addtmp16, float* %sum, align 4
  %n17 = load i32, i32* %n1, align 4
  %m18 = load float, float* %m2, align 4
  %fnegtmp19 = fneg float %m18
  %fnegtmp20 = fneg float %fnegtmp19
  %2 = sitofp i32 %n17 to float
  %addtmp21 = fadd float %2, %fnegtmp20
  store float %addtmp21, float* %result, align 4
  %result22 = load float, float* %result, align 4
  %calltmp23 = call float @print_float(float %result22)
  %sum24 = load float, float* %sum, align 4
  %result25 = load float, float* %result, align 4
  %addtmp26 = fadd float %sum24, %result25
  store float %addtmp26, float* %sum, align 4
  %n27 = load i32, i32* %n1, align 4
  %negtmp = sub i32 0, %n27
  %m28 = load float, float* %m2, align 4
  %fnegtmp29 = fneg float %m28
  %3 = sitofp i32 %negtmp to float
  %addtmp30 = fadd float %3, %fnegtmp29
  store float %addtmp30, float* %result, align 4
  %result31 = load float, float* %result, align 4
  %calltmp32 = call float @print_float(float %result31)
  %sum33 = load float, float* %sum, align 4
  %result34 = load float, float* %result, align 4
  %addtmp35 = fadd float %sum33, %result34
  store float %addtmp35, float* %sum, align 4
  %sum36 = load float, float* %sum, align 4
  ret float %sum36
}
