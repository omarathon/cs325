; ModuleID = 'mini-c'
source_filename = "mini-c"

declare i32 @print_int(i32)

define i32 @fibonacci(i32 %n) {
entry:
  %total = alloca i32, align 4
  %c = alloca i32, align 4
  %next = alloca i32, align 4
  %second = alloca i32, align 4
  %first = alloca i32, align 4
  %n1 = alloca i32, align 4
  store i32 %n, i32* %n1, align 4
  %n2 = load i32, i32* %n1, align 4
  %calltmp = call i32 @print_int(i32 %n2)
  store i32 0, i32* %first, align 4
  store i32 1, i32* %second, align 4
  store i32 1, i32* %c, align 4
  store i32 0, i32* %total, align 4
  br label %loopcond

loopcond:                                         ; preds = %ifcont, %entry
  %c3 = load i32, i32* %c, align 4
  %n4 = load i32, i32* %n1, align 4
  %lttmp = icmp ult i32 %c3, %n4
  br i1 %lttmp, label %loopbody, label %loopend

loopbody:                                         ; preds = %loopcond
  %c5 = load i32, i32* %c, align 4
  %letmp = icmp ule i32 %c5, 1
  br i1 %letmp, label %then, label %else

then:                                             ; preds = %loopbody
  %c6 = load i32, i32* %c, align 4
  store i32 %c6, i32* %next, align 4
  br label %ifcont

else:                                             ; preds = %loopbody
  %first7 = load i32, i32* %first, align 4
  %second8 = load i32, i32* %second, align 4
  %addtmp = add i32 %first7, %second8
  store i32 %addtmp, i32* %next, align 4
  %second9 = load i32, i32* %second, align 4
  store i32 %second9, i32* %first, align 4
  %next10 = load i32, i32* %next, align 4
  store i32 %next10, i32* %second, align 4
  br label %ifcont

ifcont:                                           ; preds = %else, %then
  %next11 = load i32, i32* %next, align 4
  %calltmp12 = call i32 @print_int(i32 %next11)
  %c13 = load i32, i32* %c, align 4
  %addtmp14 = add i32 %c13, 1
  store i32 %addtmp14, i32* %c, align 4
  %total15 = load i32, i32* %total, align 4
  %next16 = load i32, i32* %next, align 4
  %addtmp17 = add i32 %total15, %next16
  store i32 %addtmp17, i32* %total, align 4
  br label %loopcond

loopend:                                          ; preds = %loopcond
  %total18 = load i32, i32* %total, align 4
  %calltmp19 = call i32 @print_int(i32 %total18)
  %total20 = load i32, i32* %total, align 4
  ret i32 %total20
}
