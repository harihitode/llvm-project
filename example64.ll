; ModuleID = 'llvm_boot_camp'
source_filename = "llvm_boot_camp"

define i64 @__example(i1 %0, i64 %1, i64 %2) {
if:
br i1 %0, label %then, label %else

then:                                             ; preds = %if
%mul = mul i64 %1, %2
br label %endif

else:                                             ; preds = %if
%add = add i64 %1, %2
br label %endif

endif:                                            ; preds = %else, %then
%result = phi i64 [ %mul, %then ], [ %add, %else ]
ret i64 %result
}