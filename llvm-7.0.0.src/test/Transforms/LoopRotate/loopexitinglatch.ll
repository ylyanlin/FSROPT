; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt -S -loop-rotate < %s -verify-loop-info -verify-dom-info | FileCheck %s

target datalayout = "e-m:e-p:32:32-i64:64-v128:64:128-a:0:32-n32-S64"
target triple = "thumbv8m.base-arm-none-eabi"

%struct.List = type { %struct.List*, i32 }

define void @list_add(%struct.List** nocapture %list, %struct.List* %data) {
; CHECK-LABEL: @list_add(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[TMP0:%.*]] = load %struct.List*, %struct.List** [[LIST:%.*]], align 4
; CHECK-NEXT:    [[VAL2:%.*]] = getelementptr inbounds [[STRUCT_LIST:%.*]], %struct.List* [[TMP0]], i32 0, i32 1
; CHECK-NEXT:    [[TMP1:%.*]] = load i32, i32* [[VAL2]], align 4
; CHECK-NEXT:    [[VAL1:%.*]] = getelementptr inbounds [[STRUCT_LIST]], %struct.List* [[DATA:%.*]], i32 0, i32 1
; CHECK-NEXT:    [[TMP2:%.*]] = load i32, i32* [[VAL1]], align 4
; CHECK-NEXT:    [[CMP3:%.*]] = icmp slt i32 [[TMP1]], [[TMP2]]
; CHECK-NEXT:    br i1 [[CMP3]], label [[IF_THEN_LR_PH:%.*]], label [[IF_ELSE6:%.*]]
; CHECK:       if.then.lr.ph:
; CHECK-NEXT:    br label [[IF_THEN:%.*]]
; CHECK:       for.cond:
; CHECK-NEXT:    [[CURR_0:%.*]] = phi %struct.List* [ [[TMP5:%.*]], [[IF_THEN]] ]
; CHECK-NEXT:    [[PREV_0:%.*]] = phi %struct.List* [ [[CURR_04:%.*]], [[IF_THEN]] ]
; CHECK-NEXT:    [[VAL:%.*]] = getelementptr inbounds [[STRUCT_LIST]], %struct.List* [[CURR_0]], i32 0, i32 1
; CHECK-NEXT:    [[TMP3:%.*]] = load i32, i32* [[VAL]], align 4
; CHECK-NEXT:    [[TMP4:%.*]] = load i32, i32* [[VAL1]], align 4
; CHECK-NEXT:    [[CMP:%.*]] = icmp slt i32 [[TMP3]], [[TMP4]]
; CHECK-NEXT:    br i1 [[CMP]], label [[IF_THEN]], label [[FOR_COND_IF_ELSE6_CRIT_EDGE:%.*]]
; CHECK:       if.then:
; CHECK-NEXT:    [[CURR_04]] = phi %struct.List* [ [[TMP0]], [[IF_THEN_LR_PH]] ], [ [[CURR_0]], [[FOR_COND:%.*]] ]
; CHECK-NEXT:    [[NEXT:%.*]] = getelementptr inbounds [[STRUCT_LIST]], %struct.List* [[CURR_04]], i32 0, i32 0
; CHECK-NEXT:    [[TMP5]] = load %struct.List*, %struct.List** [[NEXT]], align 4
; CHECK-NEXT:    [[TOBOOL:%.*]] = icmp eq %struct.List* [[TMP5]], null
; CHECK-NEXT:    br i1 [[TOBOOL]], label [[IF_ELSE:%.*]], label [[FOR_COND]]
; CHECK:       if.else:
; CHECK-NEXT:    [[NEXT_LCSSA:%.*]] = phi %struct.List** [ [[NEXT]], [[IF_THEN]] ]
; CHECK-NEXT:    store %struct.List* [[DATA]], %struct.List** [[NEXT_LCSSA]], align 4
; CHECK-NEXT:    [[NEXT5:%.*]] = getelementptr inbounds [[STRUCT_LIST]], %struct.List* [[DATA]], i32 0, i32 0
; CHECK-NEXT:    store %struct.List* null, %struct.List** [[NEXT5]], align 4
; CHECK-NEXT:    br label [[FOR_END:%.*]]
; CHECK:       for.cond.if.else6_crit_edge:
; CHECK-NEXT:    [[SPLIT:%.*]] = phi %struct.List* [ [[PREV_0]], [[FOR_COND]] ]
; CHECK-NEXT:    br label [[IF_ELSE6]]
; CHECK:       if.else6:
; CHECK-NEXT:    [[PREV_0_LCSSA:%.*]] = phi %struct.List* [ [[SPLIT]], [[FOR_COND_IF_ELSE6_CRIT_EDGE]] ], [ null, [[ENTRY:%.*]] ]
; CHECK-NEXT:    [[TOBOOL7:%.*]] = icmp eq %struct.List* [[PREV_0_LCSSA]], null
; CHECK-NEXT:    br i1 [[TOBOOL7]], label [[IF_ELSE12:%.*]], label [[IF_THEN8:%.*]]
; CHECK:       if.then8:
; CHECK-NEXT:    [[NEXT9:%.*]] = getelementptr inbounds [[STRUCT_LIST]], %struct.List* [[PREV_0_LCSSA]], i32 0, i32 0
; CHECK-NEXT:    [[TMP6:%.*]] = bitcast %struct.List* [[PREV_0_LCSSA]] to i32*
; CHECK-NEXT:    [[TMP7:%.*]] = load i32, i32* [[TMP6]], align 4
; CHECK-NEXT:    [[TMP8:%.*]] = bitcast %struct.List* [[DATA]] to i32*
; CHECK-NEXT:    store i32 [[TMP7]], i32* [[TMP8]], align 4
; CHECK-NEXT:    store %struct.List* [[DATA]], %struct.List** [[NEXT9]], align 4
; CHECK-NEXT:    br label [[FOR_END]]
; CHECK:       if.else12:
; CHECK-NEXT:    [[TMP9:%.*]] = bitcast %struct.List** [[LIST]] to i32*
; CHECK-NEXT:    [[TMP10:%.*]] = load i32, i32* [[TMP9]], align 4
; CHECK-NEXT:    [[TMP11:%.*]] = bitcast %struct.List* [[DATA]] to i32*
; CHECK-NEXT:    store i32 [[TMP10]], i32* [[TMP11]], align 4
; CHECK-NEXT:    store %struct.List* [[DATA]], %struct.List** [[LIST]], align 4
; CHECK-NEXT:    br label [[FOR_END]]
; CHECK:       for.end:
; CHECK-NEXT:    ret void
;
entry:
  %0 = load %struct.List*, %struct.List** %list, align 4
  br label %for.cond

for.cond:                                         ; preds = %if.then, %entry
  %curr.0 = phi %struct.List* [ %0, %entry ], [ %3, %if.then ]
  %prev.0 = phi %struct.List* [ null, %entry ], [ %curr.0, %if.then ]
  %val = getelementptr inbounds %struct.List, %struct.List* %curr.0, i32 0, i32 1
  %1 = load i32, i32* %val, align 4
  %val1 = getelementptr inbounds %struct.List, %struct.List* %data, i32 0, i32 1
  %2 = load i32, i32* %val1, align 4
  %cmp = icmp slt i32 %1, %2
  br i1 %cmp, label %if.then, label %if.else6

if.then:                                          ; preds = %for.cond
  %next = getelementptr inbounds %struct.List, %struct.List* %curr.0, i32 0, i32 0
  %3 = load %struct.List*, %struct.List** %next, align 4
  %tobool = icmp eq %struct.List* %3, null
  br i1 %tobool, label %if.else, label %for.cond

if.else:                                          ; preds = %if.then
  %next.lcssa = phi %struct.List** [ %next, %if.then ]
  store %struct.List* %data, %struct.List** %next.lcssa, align 4
  %next5 = getelementptr inbounds %struct.List, %struct.List* %data, i32 0, i32 0
  store %struct.List* null, %struct.List** %next5, align 4
  br label %for.end

if.else6:                                         ; preds = %for.cond
  %prev.0.lcssa = phi %struct.List* [ %prev.0, %for.cond ]
  %tobool7 = icmp eq %struct.List* %prev.0.lcssa, null
  br i1 %tobool7, label %if.else12, label %if.then8

if.then8:                                         ; preds = %if.else6
  %next9 = getelementptr inbounds %struct.List, %struct.List* %prev.0.lcssa, i32 0, i32 0
  %4 = bitcast %struct.List* %prev.0.lcssa to i32*
  %5 = load i32, i32* %4, align 4
  %6 = bitcast %struct.List* %data to i32*
  store i32 %5, i32* %6, align 4
  store %struct.List* %data, %struct.List** %next9, align 4
  br label %for.end

if.else12:                                        ; preds = %if.else6
  %7 = bitcast %struct.List** %list to i32*
  %8 = load i32, i32* %7, align 4
  %9 = bitcast %struct.List* %data to i32*
  store i32 %8, i32* %9, align 4
  store %struct.List* %data, %struct.List** %list, align 4
  br label %for.end

for.end:                                          ; preds = %if.else12, %if.then8, %if.else
  ret void
}

define i32 @test2(i32* %l) {
; CHECK-LABEL: @test2(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[TMP0:%.*]] = load i32, i32* [[L:%.*]], align 4
; CHECK-NEXT:    [[TOBOOL2:%.*]] = icmp eq i32 [[TMP0]], 0
; CHECK-NEXT:    br i1 [[TOBOOL2]], label [[CLEANUP:%.*]], label [[DO_COND_LR_PH:%.*]]
; CHECK:       do.cond.lr.ph:
; CHECK-NEXT:    br label [[DO_COND:%.*]]
; CHECK:       do.body:
; CHECK-NEXT:    [[A_0:%.*]] = phi i32 [ [[REM:%.*]], [[DO_COND]] ]
; CHECK-NEXT:    [[TMP1:%.*]] = load i32, i32* [[L]], align 4
; CHECK-NEXT:    [[TOBOOL:%.*]] = icmp eq i32 [[TMP1]], 0
; CHECK-NEXT:    br i1 [[TOBOOL]], label [[DO_BODY_CLEANUP_CRIT_EDGE:%.*]], label [[DO_COND]]
; CHECK:       do.body.cleanup_crit_edge:
; CHECK-NEXT:    [[SPLIT:%.*]] = phi i32 [ [[A_0]], [[DO_BODY:%.*]] ]
; CHECK-NEXT:    br label [[CLEANUP]]
; CHECK:       cleanup:
; CHECK-NEXT:    [[A_0_LCSSA:%.*]] = phi i32 [ [[SPLIT]], [[DO_BODY_CLEANUP_CRIT_EDGE]] ], [ 100, [[ENTRY:%.*]] ]
; CHECK-NEXT:    store i32 10, i32* [[L]], align 4
; CHECK-NEXT:    br label [[CLEANUP2:%.*]]
; CHECK:       do.cond:
; CHECK-NEXT:    [[TMP2:%.*]] = phi i32 [ [[TMP0]], [[DO_COND_LR_PH]] ], [ [[TMP1]], [[DO_BODY]] ]
; CHECK-NEXT:    [[MUL:%.*]] = mul nsw i32 [[TMP2]], 13
; CHECK-NEXT:    [[REM]] = srem i32 [[MUL]], 27
; CHECK-NEXT:    [[TMP3:%.*]] = load i32, i32* [[L]], align 4
; CHECK-NEXT:    [[TOBOOL1:%.*]] = icmp eq i32 [[TMP3]], 0
; CHECK-NEXT:    br i1 [[TOBOOL1]], label [[CLEANUP2_LOOPEXIT:%.*]], label [[DO_BODY]]
; CHECK:       cleanup2.loopexit:
; CHECK-NEXT:    br label [[CLEANUP2]]
; CHECK:       cleanup2:
; CHECK-NEXT:    [[RETVAL_2:%.*]] = phi i32 [ [[A_0_LCSSA]], [[CLEANUP]] ], [ 0, [[CLEANUP2_LOOPEXIT]] ]
; CHECK-NEXT:    ret i32 [[RETVAL_2]]
;
entry:
  br label %do.body

do.body:                                          ; preds = %do.cond, %entry
  %a.0 = phi i32 [ 100, %entry ], [ %rem, %do.cond ]
  %0 = load i32, i32* %l, align 4
  %tobool = icmp eq i32 %0, 0
  br i1 %tobool, label %cleanup, label %do.cond

cleanup:                                          ; preds = %do.body
  %a.0.lcssa = phi i32 [ %a.0, %do.body ]
  store i32 10, i32* %l, align 4
  br label %cleanup2

do.cond:                                          ; preds = %do.body
  %mul = mul nsw i32 %0, 13
  %rem = srem i32 %mul, 27
  %1 = load i32, i32* %l, align 4
  %tobool1 = icmp eq i32 %1, 0
  br i1 %tobool1, label %cleanup2.loopexit, label %do.body

cleanup2.loopexit:                                ; preds = %do.cond
  br label %cleanup2

cleanup2:                                         ; preds = %cleanup2.loopexit, %cleanup
  %retval.2 = phi i32 [ %a.0.lcssa, %cleanup ], [ 0, %cleanup2.loopexit ]
  ret i32 %retval.2
}

define i32 @no_rotate(i32* %l) {
; CHECK-LABEL: @no_rotate(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    br label [[DO_BODY:%.*]]
; CHECK:       do.body:
; CHECK-NEXT:    [[A_0:%.*]] = phi i32 [ 100, [[ENTRY:%.*]] ], [ [[REM:%.*]], [[DO_COND:%.*]] ]
; CHECK-NEXT:    [[TMP0:%.*]] = load i32, i32* [[L:%.*]], align 4
; CHECK-NEXT:    [[TOBOOL:%.*]] = icmp eq i32 [[TMP0]], 0
; CHECK-NEXT:    br i1 [[TOBOOL]], label [[CLEANUP:%.*]], label [[DO_COND]]
; CHECK:       cleanup:
; CHECK-NEXT:    [[A_0_LCSSA:%.*]] = phi i32 [ [[A_0]], [[DO_BODY]] ]
; CHECK-NEXT:    store i32 10, i32* [[L]], align 4
; CHECK-NEXT:    br label [[CLEANUP2:%.*]]
; CHECK:       do.cond:
; CHECK-NEXT:    [[MUL:%.*]] = mul nsw i32 [[A_0]], 13
; CHECK-NEXT:    [[REM]] = srem i32 [[MUL]], 27
; CHECK-NEXT:    [[TMP1:%.*]] = load i32, i32* [[L]], align 4
; CHECK-NEXT:    [[TOBOOL1:%.*]] = icmp eq i32 [[TMP1]], 0
; CHECK-NEXT:    br i1 [[TOBOOL1]], label [[CLEANUP2_LOOPEXIT:%.*]], label [[DO_BODY]]
; CHECK:       cleanup2.loopexit:
; CHECK-NEXT:    br label [[CLEANUP2]]
; CHECK:       cleanup2:
; CHECK-NEXT:    [[RETVAL_2:%.*]] = phi i32 [ [[A_0_LCSSA]], [[CLEANUP]] ], [ 0, [[CLEANUP2_LOOPEXIT]] ]
; CHECK-NEXT:    ret i32 [[RETVAL_2]]
;
entry:
  br label %do.body

do.body:                                          ; preds = %do.cond, %entry
  %a.0 = phi i32 [ 100, %entry ], [ %rem, %do.cond ]
  %0 = load i32, i32* %l, align 4
  %tobool = icmp eq i32 %0, 0
  br i1 %tobool, label %cleanup, label %do.cond

cleanup:                                          ; preds = %do.body
  %a.0.lcssa = phi i32 [ %a.0, %do.body ]
  store i32 10, i32* %l, align 4
  br label %cleanup2

do.cond:                                          ; preds = %do.body
  %mul = mul nsw i32 %a.0, 13
  %rem = srem i32 %mul, 27
  %1 = load i32, i32* %l, align 4
  %tobool1 = icmp eq i32 %1, 0
  br i1 %tobool1, label %cleanup2.loopexit, label %do.body

cleanup2.loopexit:                                ; preds = %do.cond
  br label %cleanup2

cleanup2:                                         ; preds = %cleanup2.loopexit, %cleanup
  %retval.2 = phi i32 [ %a.0.lcssa, %cleanup ], [ 0, %cleanup2.loopexit ]
  ret i32 %retval.2
}
