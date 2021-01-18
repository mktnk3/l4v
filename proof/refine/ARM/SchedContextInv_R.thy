(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory SchedContextInv_R
imports Ipc_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

primrec valid_sc_inv' :: "sched_context_invocation \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_sc_inv' (InvokeSchedContextConsumed scptr args) = (sc_at' scptr and ex_nonz_cap_to' scptr)"
| "valid_sc_inv' (InvokeSchedContextBind scptr cap) =
     (ex_nonz_cap_to' scptr and valid_cap' cap and
        (case cap of
           ThreadCap t \<Rightarrow>
             ex_nonz_cap_to' t and
             bound_sc_tcb_at' ((=) None) t and
             obj_at' (\<lambda>sc. scTCB sc = None) scptr \<^cancel>\<open> and
             FIXME RT: can hopefully be established via assertions:
             (\<lambda>s. st_tcb_at' (ipc_queued_thread_state) t s
                     \<longrightarrow> sc_at_pred' (sc_released (cur_time s)) scptr s) \<close>
         | NotificationCap n _ _ _ \<Rightarrow>
             ex_nonz_cap_to' n and
             obj_at' (\<lambda>ntfn. ntfnSc ntfn = None) n and
             obj_at' (\<lambda>sc. scNtfn sc = None) scptr
         | _ \<Rightarrow> \<bottom>))"
| "valid_sc_inv' (InvokeSchedContextUnbindObject scptr cap) =
     (ex_nonz_cap_to' scptr and valid_cap' cap and
        (case cap of
           ThreadCap t \<Rightarrow>
             ex_nonz_cap_to' t and obj_at' (\<lambda>sc. scTCB sc = Some t) scptr and
             (\<lambda>s. t \<noteq> ksCurThread s)
         | NotificationCap n _ _ _ \<Rightarrow>
             ex_nonz_cap_to' n and obj_at' (\<lambda>sc. scNtfn sc = Some n) scptr
         | _ \<Rightarrow> \<bottom>))"
| "valid_sc_inv' (InvokeSchedContextUnbind scptr) = (sc_at' scptr and ex_nonz_cap_to' scptr)"
| "valid_sc_inv' (InvokeSchedContextYieldTo scptr args) =
     (\<lambda>s. ex_nonz_cap_to' scptr s \<and>
          (\<forall>ct. ct = ksCurThread s \<longrightarrow>
                bound_yt_tcb_at' ((=) None) ct s \<and>
                obj_at' (\<lambda>sc. \<exists>t. scTCB sc = Some t \<and> t \<noteq> ct) scptr s))"

(* FIXME RT: valid_refills_number is probably wrong for Haskell *)
primrec valid_sc_ctrl_inv' :: "sched_control_invocation \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_sc_ctrl_inv' (InvokeSchedControlConfigure scptr budget period mrefills badge) =
     ((\<lambda>s. \<exists>n. sc_at'_n n scptr s \<and> valid_refills_number mrefills n) and
      ex_nonz_cap_to' scptr and K (MIN_REFILLS \<le> mrefills) and
      K (budget \<le> MAX_SC_PERIOD \<and> budget \<ge> MIN_BUDGET \<and>
         period \<le> MAX_SC_PERIOD \<and> budget \<ge> MIN_BUDGET \<and>
         budget \<le> period))"

primrec sc_inv_rel :: "Invocations_A.sched_context_invocation \<Rightarrow> sched_context_invocation \<Rightarrow> bool"
  where
  "sc_inv_rel (Invocations_A.InvokeSchedContextConsumed sc bf) sci' =
   (sci' = InvokeSchedContextConsumed sc bf)"
| "sc_inv_rel (Invocations_A.InvokeSchedContextBind sc cap) sci' =
   (\<exists>cap'. cap_relation cap cap' \<and> sci' = InvokeSchedContextBind sc cap')"
| "sc_inv_rel (Invocations_A.InvokeSchedContextUnbindObject sc cap) sci' =
   (\<exists>cap'. cap_relation cap cap' \<and> sci' = InvokeSchedContextUnbindObject sc cap')"
| "sc_inv_rel (Invocations_A.InvokeSchedContextUnbind sc cap) sci' =
   (sci' = InvokeSchedContextUnbind sc)" \<comment> \<open>FIXME RT: remove cap in abstract InvokeSchedContextUnbind\<close>
| "sc_inv_rel (Invocations_A.InvokeSchedContextYieldTo sc bf) sci' =
   (sci' = InvokeSchedContextYieldTo sc bf)"

primrec sc_ctrl_inv_rel ::
  "Invocations_A.sched_control_invocation \<Rightarrow> sched_control_invocation \<Rightarrow> bool" where
  "sc_ctrl_inv_rel (Invocations_A.InvokeSchedControlConfigure sc budget period refills badge) sci' =
    (sci' = InvokeSchedControlConfigure sc budget period refills badge)"

lemma decodeSchedContext_Bind_wf:
  "\<lbrace> valid_cap' (SchedContextCap sc n) and ex_nonz_cap_to' sc and
     (\<lambda>s. \<forall>cap\<in>set excaps. \<forall>r\<in>zobj_refs' cap. ex_nonz_cap_to' r s) and
     (\<lambda>s. \<forall>x\<in>set excaps. valid_cap' x s) \<rbrace>
   decodeSchedContext_Bind sc excaps
   \<lbrace>valid_sc_inv'\<rbrace>, -"
  apply (clarsimp simp: decodeSchedContext_Bind_def)
  apply (wpsimp wp: gts_wp' threadGet_wp getNotification_wp
              simp: scReleased_def scActive_def isBlocked_def refillReady_def)
  apply (clarsimp simp: valid_cap'_def)
  apply (drule_tac x="hd excaps" in bspec, fastforce dest: hd_in_set)+
  apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  done

lemma decodeSchedContext_UnbindObject_wf:
  "\<lbrace> valid_cap' (SchedContextCap sc n) and ex_nonz_cap_to' sc and
     (\<lambda>s. \<forall>cap\<in>set excaps. \<forall>r\<in>zobj_refs' cap. ex_nonz_cap_to' r s) and
     (\<lambda>s. \<forall>x\<in>set excaps. valid_cap' x s) \<rbrace>
   decodeSchedContext_UnbindObject sc excaps
   \<lbrace>valid_sc_inv'\<rbrace>, -"
  apply (clarsimp simp: decodeSchedContext_UnbindObject_def)
  apply (wpsimp wp: gts_wp' threadGet_wp getNotification_wp
              simp: scReleased_def scActive_def isBlocked_def refillReady_def)
  apply (clarsimp simp: valid_cap'_def)
  apply (drule_tac x="hd excaps" in bspec, fastforce dest: hd_in_set)+
  apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  done

lemma decodeSchedContext_YieldTo_wf:
  "\<lbrace> valid_cap' (SchedContextCap sc n) and ex_nonz_cap_to' sc \<rbrace>
   decodeSchedContext_YieldTo sc args
   \<lbrace>valid_sc_inv'\<rbrace>, -"
  apply (clarsimp simp: decodeSchedContext_YieldTo_def)
  apply (wpsimp wp: gts_wp' threadGet_wp getNotification_wp getTCB_wp
              simp: scReleased_def scActive_def isBlocked_def refillReady_def)
  apply (clarsimp simp: valid_cap'_def)
  apply (clarsimp simp: pred_tcb_at'_def obj_at'_def projectKOs)
  done

lemma valid_SchedContextCap_sc_at':
  "\<lbrakk>valid_cap' (capability.SchedContextCap sc n) s\<rbrakk> \<Longrightarrow> sc_at' sc s"
  apply (clarsimp simp: valid_cap'_def obj_at'_real_def)
  apply (rule ko_wp_at'_weakenE)
   apply (fastforce simp: objBits_simps
                   split: kernel_object.splits)+
  done

(* FIXME RT: preconditions can be reduced, this is what is available at the call site: *)
lemma decodeSchedContextInvocation_wf:
  "\<lbrace> valid_cap' (SchedContextCap sc n) and ex_nonz_cap_to' sc and
     (\<lambda>s. \<forall>cap\<in>set excaps. \<forall>r\<in>zobj_refs' cap. ex_nonz_cap_to' r s) and
     (\<lambda>s. \<forall>x\<in>set excaps. valid_cap' x s) \<rbrace>
   decodeSchedContextInvocation label sc excaps args
   \<lbrace>valid_sc_inv'\<rbrace>, -"
  apply (simp add: decodeSchedContextInvocation_def)
  apply (wpsimp wp: decodeSchedContext_Bind_wf[where n=n]
                    decodeSchedContext_UnbindObject_wf[where n=n]
                    decodeSchedContext_YieldTo_wf[where n=n])
  apply (fastforce dest: valid_SchedContextCap_sc_at')
  done

(* FIXME RT: preconditions can be reduced, this is what is available at the call site: *)
lemma decodeSchedControlInvocation_wf:
  "\<lbrace> invs' and sch_act_simple and
     (\<lambda>s. \<forall>cap\<in>set excaps. \<forall>r\<in>zobj_refs' cap. ex_nonz_cap_to' r s) and
     (\<lambda>s. \<forall>x\<in>set excaps. valid_cap' x s) \<rbrace>
   decodeSchedControlInvocation label args excaps
   \<lbrace>valid_sc_ctrl_inv'\<rbrace>, -"
thm  decode_sched_control_invocation_def decodeSchedControlInvocation_def[unfolded decodeSchedControl_Configure_def]
thm decodeSchedControl_Configure_def
thm refillAbsoluteMax_def refillAbsoluteMax'_def
find_theorems refillAbsoluteMax'
  apply (simp add: decodeSchedControlInvocation_def decodeSchedControl_Configure_def Let_def split_def)
thm decodeSchedControl_Configure_def
find_theorems decode_sched_control_invocation
thm parseTimeArg_def
apply (wpsimp simp: decodeSchedControl_Configure_def timeArgSize_def)

apply safe
defer

  apply (drule_tac x="hd excaps" in bspec, fastforce)
apply (cases "hd excaps"; clarsimp simp: isSchedContextCap_def)

apply (clarsimp simp: MIN_REFILLS_def minRefills_def)



  apply (clarsimp simp: valid_cap'_def capSchedContextPtr_def)
  apply (drule_tac x="hd excaps" in bspec, fastforce dest: hd_in_set)+

  apply (fastforce simp: pred_tcb_at'_def obj_at'_def)
  apply (clarsimp simp: valid_cap'_def)
  apply (drule_tac x="hd excaps" in bspec, fastforce dest: hd_in_set)+
  apply (fastforce simp: pred_tcb_at'_def obj_at'_def)

lemma decode_sc_inv_corres:
  "list_all2 cap_relation excaps excaps' \<Longrightarrow>
   corres (ser \<oplus> sc_inv_rel)
          (invs and valid_sched and sc_at sc and (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> x))
          (invs' and (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' x s))
          (decode_sched_context_invocation (mi_label mi) sc excaps args')
          (decodeSchedContextInvocation (mi_label mi) sc excaps' args')"
  sorry

lemma decode_sc_ctrl_inv_corres:
  "list_all2 cap_relation excaps excaps' \<Longrightarrow>
   corres (ser \<oplus> sc_ctrl_inv_rel)
           (invs and valid_sched  and (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> x ))
           (invs' and (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' x s))
           (decode_sched_control_invocation (mi_label mi) args' excaps)
           (decodeSchedControlInvocation (mi_label mi) args' excaps')"
  sorry

(* FIXME RT: preconditions can be reduced, this is what is available at the call site: *)
lemma invoke_sched_context_corres:
  "sc_inv_rel sc_inv sc_inv' \<Longrightarrow>
   corres (=)
          (einvs and valid_sched_context_inv sc_inv and simple_sched_action and ct_active)
          (invs' and sch_act_simple and valid_sc_inv' sc_inv' and ct_active')
          (invoke_sched_context sc_inv)
          (invokeSchedContext sc_inv')"
  apply (simp add: invoke_sched_context_def invokeSchedContext_def)
  (* most of the next layer down should go into SchedContext_R, because some of these are
     reused in Finalise and IpcCancel *)
  sorry


(* FIXME RT: preconditions can be reduced, this is what is available at the call site: *)
lemma invoke_sched_control_configure_corres:
  "sc_ctrl_inv_rel sc_inv sc_inv' \<Longrightarrow>
   corres (=)
          (einvs and valid_sched_control_inv sc_inv and simple_sched_action and ct_active)
          (invs' and sch_act_simple and valid_sc_ctrl_inv' sc_inv' and ct_active')
          (invoke_sched_control_configure sc_inv)
          (invokeSchedControlConfigure sc_inv')"
  apply (cases sc_inv)
  apply (simp add: invoke_sched_control_configure_def invokeSchedControlConfigure_def)
  sorry

end

end
