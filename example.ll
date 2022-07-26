; ModuleID = 'llvm_boot_camp'
source_filename = "llvm_boot_camp"

define i32 @__example(i1 %0, i32 %1, i32 %2) {
if:
br i1 %0, label %then, label %else

then:                                             ; preds = %if
%mul = mul i32 %1, %2
br label %endif

else:                                             ; preds = %if
%add = add i32 %1, %2
br label %endif

endif:                                            ; preds = %else, %then
%result = phi i32 [ %mul, %then ], [ %add, %else ]
ret i32 %result
}