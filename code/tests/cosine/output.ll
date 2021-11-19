; ModuleID = 'mini-c'
source_filename = "mini-c"

declare float @print_float(float)

define float @cosine(float %x) {
entry:
  %alt = alloca float, align 4
  %eps = alloca float, align 4
  %term = alloca float, align 4
  %n = alloca float, align 4
  %cos = alloca float, align 4
  %x1 = alloca float, align 4
  store float %x, float* %x1, align 4
  store float 0x3EB0C6F7A0000000, float* %eps, align 4
  store float 1.000000e+00, float* %n, align 4
  store float 1.000000e+00, float* %cos, align 4
  store float 1.000000e+00, float* %term, align 4
  store float -1.000000e+00, float* %alt, align 4
  br label %loopcond

loopcond:                                         ; preds = %loopbody, %entry
  %term2 = load float, float* %term, align 4
  %eps3 = load float, float* %eps, align 4
  %gttmp = fcmp ugt float %term2, %eps3
  br i1 %gttmp, label %loopbody, label %loopend

loopbody:                                         ; preds = %loopcond
  %term4 = load float, float* %term, align 4
  %x5 = load float, float* %x1, align 4
  %multmp = fmul float %term4, %x5
  %x6 = load float, float* %x1, align 4
  %multmp7 = fmul float %multmp, %x6
  %n8 = load float, float* %n, align 4
  %divtmp = fdiv float %multmp7, %n8
  %n9 = load float, float* %n, align 4
  %addtmp = fadd float %n9, 1.000000e+00
  %divtmp10 = fdiv float %divtmp, %addtmp
  store float %divtmp10, float* %term, align 4
  %cos11 = load float, float* %cos, align 4
  %alt12 = load float, float* %alt, align 4
  %term13 = load float, float* %term, align 4
  %multmp14 = fmul float %alt12, %term13
  %addtmp15 = fadd float %cos11, %multmp14
  store float %addtmp15, float* %cos, align 4
  %alt16 = load float, float* %alt, align 4
  %fnegtmp = fneg float %alt16
  store float %fnegtmp, float* %alt, align 4
  %n17 = load float, float* %n, align 4
  %addtmp18 = fadd float %n17, 2.000000e+00
  store float %addtmp18, float* %n, align 4
  br label %loopcond

loopend:                                          ; preds = %loopcond
  %cos19 = load float, float* %cos, align 4
  %calltmp = call float @print_float(float %cos19)
  %cos20 = load float, float* %cos, align 4
  ret float %cos20
}
