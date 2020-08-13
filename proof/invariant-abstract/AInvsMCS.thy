(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
The main theorem
*)

theory AInvsMCS
imports "./$L4V_ARCH/ArchDetSchedSchedule_AI"
begin


(***)

method is_schedulable_bool_unfold =
    clarsimp simp: is_schedulable_bool_def is_sc_active_def get_tcb_def in_release_queue_def
            split: option.splits kernel_object.splits

lemma is_schedulable_bool_machine_state_update[iff]:
  "is_schedulable_bool t (machine_state_update f s) = is_schedulable_bool t s"
  by is_schedulable_bool_unfold

lemma is_schedulable_bool_domain_time_update[iff]:
  "is_schedulable_bool t (domain_time_update f s) = is_schedulable_bool t s"
  by is_schedulable_bool_unfold

lemma is_schedulable_bool_consumed_time_update[iff]:
  "is_schedulable_bool t (consumed_time_update f s) = is_schedulable_bool t s"
  by is_schedulable_bool_unfold

lemma is_schedulable_bool_scheduler_action_update[iff]:
  "is_schedulable_bool t (scheduler_action_update f s) = is_schedulable_bool t s"
  by is_schedulable_bool_unfold

lemma is_schedulable_bool_reprogram_timer_update[iff]:
  "is_schedulable_bool t (reprogram_timer_update f s) = is_schedulable_bool t s"
  by is_schedulable_bool_unfold

lemma is_schedulable_bool_ready_queues_update[iff]:
  "is_schedulable_bool t (ready_queues_update f s) = is_schedulable_bool t s"
  by is_schedulable_bool_unfold

lemma is_schedulable_bool_cur_thread_update[iff]:
  "is_schedulable_bool t (cur_thread_update f s) = is_schedulable_bool t s"
  by is_schedulable_bool_unfold

lemma is_schedulable_bool_cur_sc_update[iff]:
  "is_schedulable_bool t (cur_sc_update f s) = is_schedulable_bool t s"
  by is_schedulable_bool_unfold

lemma is_schedulable_bool_cur_domain_update[iff]:
  "is_schedulable_bool t (cur_domain_update f s) = is_schedulable_bool t s"
  by is_schedulable_bool_unfold

lemma is_schedulable_bool_domain_index_update[iff]:
  "is_schedulable_bool t (domain_index_update f s) = is_schedulable_bool t s"
  by is_schedulable_bool_unfold

lemma is_schedulable_bool_more_update[iff]:
  "is_schedulable_bool t (trans_state f s) = is_schedulable_bool t s"
  by is_schedulable_bool_unfold

crunches set_next_interrupt, commit_domain_time, is_round_robin, tcb_sched_action,
         possible_switch_to, next_domain
  for is_schedulable_bool[wp]: "is_schedulable_bool tp"
  and ct_schedulable[wp]: ct_schedulable
  (simp: crunch_simps wp: crunch_wps)

lemma set_refills_ct_schedulable[wp]:
  "set_refills scp refills \<lbrace>ct_schedulable\<rbrace>"
  apply (wpsimp wp: set_refills_wp simp: obj_at_def)
  by is_schedulable_bool_unfold fastforce

lemma sc_consumed_update_ct_schedulable[wp]: (* for commit_time *)
  "update_sched_context scp (\<lambda>sc. sc\<lparr>sc_consumed := sc_consumed sc + consumed\<rparr>) \<lbrace>ct_schedulable\<rbrace>"
  apply (wpsimp wp: update_sched_context_wp simp: obj_at_def)
  by is_schedulable_bool_unfold fastforce

lemma refill_budget_check_round_robin_ct_schedulable[wp]:
  "refill_budget_check_round_robin consumed \<lbrace>ct_schedulable\<rbrace>"
  unfolding refill_budget_check_round_robin_def
  supply if_split[split del]
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imps)

lemma refill_budget_check_ct_schedulable[wp]:
  "refill_budget_check consumed \<lbrace>ct_schedulable\<rbrace>"
  unfolding refill_budget_check_def
  supply if_split[split del]
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imps)

lemma refill_unblock_check_ct_schedulable[wp]:
  "refill_unblock_check consumed \<lbrace>ct_schedulable\<rbrace>"
  unfolding refill_unblock_check_def
  supply if_split[split del]
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imps)

lemma commit_time_ct_schedulable[wp]:
  "commit_time \<lbrace>ct_schedulable\<rbrace>"
  unfolding commit_time_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps)

lemma switch_sched_context_ct_schedulable[wp]:
  "switch_sched_context \<lbrace>ct_schedulable\<rbrace>"
  unfolding switch_sched_context_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps)

lemma sc_and_timer_ct_schedulable[wp]:
  "sc_and_timer \<lbrace>ct_schedulable\<rbrace>"
  unfolding sc_and_timer_def by wpsimp

lemma awaken_ct_schedulable[wp]:
  "awaken \<lbrace>ct_schedulable\<rbrace>"
  apply (wpsimp simp: awaken_def wp: mapM_x_wp_inv hoare_drop_imp)
  apply is_schedulable_bool_unfold
  by (meson in_set_dropD; fastforce)

crunches next_domain
  for ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  (wp: crunch_wps simp: crunch_simps)


(* something similar/same exists in DetSchedSchedule_AI *)
lemma enqueue_thread_queued:
  "\<lbrace>\<top>\<rbrace> tcb_sched_action tcb_sched_enqueue thread \<lbrace>\<lambda>_ s. \<exists>d prio. thread \<in> set (ready_queues s d prio)\<rbrace>"
  unfolding tcb_sched_action_def get_tcb_queue_def bind_assoc set_tcb_queue_def
  apply (wpsimp simp:  wp: thread_get_wp')
  by (fastforce simp: obj_at_def tcb_sched_enqueue_def)

definition ready_or_release where
    "ready_or_release s \<equiv> \<forall>t. \<not> ((\<exists>d p. t \<in> set (ready_queues s d p)) \<and> t \<in> set (release_queue s))"

abbreviation ct_in_cur_domain where
  "ct_in_cur_domain s \<equiv> obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_domain tcb = cur_domain s) (cur_thread s) s"

definition valid_ready_queues where
  "valid_ready_queues s \<equiv>
      \<forall>p d . \<forall>t \<in> set (ready_queues s p d).
                obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_priority tcb = p \<and> tcb_domain tcb = d
                                     \<and> runnable (tcb_state tcb)
                                     \<and> (\<exists>scp. tcb_sched_context tcb = Some scp \<and> is_sc_active scp s)) t s"
locale ct_schedulable_locale =
    fixes state_ext :: "('a::state_ext) itself"
    assumes arch_stt_is_schedulable_bool [wp]:
      "\<And>t' t. \<lbrace>is_schedulable_bool t\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. (is_schedulable_bool t :: 'a state \<Rightarrow> bool)\<rbrace>"
    assumes arch_stt_ct_schedulable [wp]:
      "\<And>t'. \<lbrace>ct_schedulable\<rbrace> arch_switch_to_thread t' \<lbrace>\<lambda>_. (ct_schedulable :: 'a state \<Rightarrow> bool)\<rbrace>"
    assumes arch_stit_is_schedulable_bool [wp]:
      "\<And>t. \<lbrace>is_schedulable_bool t\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. (is_schedulable_bool t :: 'a state \<Rightarrow> bool)\<rbrace>"
    assumes arch_stit_ct_schedulable [wp]:
      "\<lbrace>ct_schedulable\<rbrace> arch_switch_to_idle_thread \<lbrace>\<lambda>_. (ct_schedulable :: 'a state \<Rightarrow> bool)\<rbrace>"
begin

lemma switch_to_thread_ct_schedulable[wp]:
  "\<lbrace>is_schedulable_bool tp\<rbrace> switch_to_thread tp \<lbrace>\<lambda>_. (ct_schedulable :: 'a state \<Rightarrow> bool)\<rbrace>"
  unfolding switch_to_thread_def by wpsimp

crunches switch_to_idle_thread
  for is_schedulable_bool[wp]: "is_schedulable_bool tp :: 'a state \<Rightarrow> bool"
  (simp: crunch_simps wp: crunch_wps ignore: arch_switch_to_idle_thread)

crunches guarded_switch_to
  for is_schedulable_bool[wp]: "is_schedulable_bool tp :: 'a state \<Rightarrow> bool"
  (simp: crunch_simps wp: crunch_wps)

lemma guarded_switch_to_ct_schedulable[wp]:
  "\<lbrace>is_schedulable_bool tp\<rbrace> guarded_switch_to tp \<lbrace>\<lambda>_. (ct_schedulable :: 'a state \<Rightarrow> bool)\<rbrace>"
  unfolding guarded_switch_to_def by (wpsimp wp: is_schedulable_wp)

thm max_non_empty_queue_def guarded_switch_to_def

lemma choose_thread_ct_schedulable:
  "\<lbrace>\<lambda>s. max_non_empty_queue (ready_queues s (cur_domain s)) \<noteq> []
        \<and> is_schedulable_bool (hd (max_non_empty_queue (ready_queues s (cur_domain s)))) s\<rbrace>
    choose_thread
   \<lbrace>\<lambda>_. ct_schedulable :: 'a state \<Rightarrow> bool\<rbrace>"
  unfolding choose_thread_def
  supply if_split[split del]
  apply (rule hoare_seq_ext[OF _ hoare_gets_sp])
  apply (rule hoare_seq_ext[OF _ hoare_gets_sp])
  apply (wpsimp simp: set_scheduler_action_def)
  apply (rule hoare_pre_cont)
  apply wpsimp
  apply clarsimp
  using max_non_empty_queue_def by auto

thm choose_thread_def guarded_switch_to_def switch_to_thread_def
(*
max_non_empty_queue (ready_queues s (cur_domain s)) \<noteq> []
        \<and> 
*)
lemma schedule_choose_new_thread_ct_schedulable:
  "\<lbrace>\<lambda>s. is_schedulable_bool (hd (max_non_empty_queue (ready_queues s (cur_domain s)))) s\<rbrace>
    schedule_choose_new_thread
   \<lbrace>\<lambda>_. ct_schedulable :: 'a state \<Rightarrow> bool\<rbrace>"
  unfolding schedule_choose_new_thread_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp simp: set_scheduler_action_def Let_def
           wp: choose_thread_ct_schedulable hoare_vcg_conj_lift)


lemma "schedule_choose_new_thread \<lbrace>ct_schedulable :: 'a state \<Rightarrow> bool\<rbrace>"
  unfolding schedule_choose_new_thread_def
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (wpsimp simp: set_scheduler_action_def Let_def
           wp: choose_thread_ct_schedulable)
  apply (intro conjI impI)

lemma schedule_ct_schedulable:
  "\<lbrace>ct_schedulable\<rbrace> Schedule_A.schedule \<lbrace>\<lambda>rv. ct_schedulable :: 'a state \<Rightarrow> bool\<rbrace>"
  unfolding schedule_def
  apply (rule hoare_seq_ext[OF _ awaken_ct_schedulable])
  apply simp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp'])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; simp add: bind_assoc)
  apply wpsimp


defer

apply (rule_tac Q="(\<lambda>s. ct_schedulable = is_schedulable_bool ct s) and
        ((\<lambda>s. is_schedulable_bool (cur_thread s) s) and
         (\<lambda>s. cur_thread s = ct)) and K ct_schedulable and
        (\<lambda>s. scheduler_action s = choose_new_thread)" in hoare_weaken_pre[rotated])
apply clarsimp
apply (clarsimp simp: when_def)

apply (wpsimp wp: schedule_choose_new_thread_ct_schedulable)
subgoal sorry


apply (rename_tac candidate)
apply (rule_tac Q="(\<lambda>s. ct_schedulable = is_schedulable_bool ct s) and
        ((\<lambda>s. is_schedulable_bool (cur_thread s) s) and
         (\<lambda>s. cur_thread s = ct)) and K ct_schedulable and
        (\<lambda>s. scheduler_action s = switch_thread candidate)" in hoare_weaken_pre[rotated])
apply clarsimp
apply (clarsimp simp: when_def)
thm hoare_seq_ext
apply (rule_tac B="\<lambda>_. (is_schedulable_bool ct and
        ((\<lambda>s. is_schedulable_bool (cur_thread s) s) and
         (\<lambda>s. cur_thread s = ct)) and
        (\<lambda>s. scheduler_action s = switch_thread candidate) and
         (\<lambda>s. \<exists>d prio. ct \<in> set (ready_queues s d prio)))" in hoare_seq_ext[rotated])
apply (wpsimp wp: enqueue_thread_queued)
apply (rule hoare_seq_ext[OF _ gets_sp])
apply (rename_tac it)
apply (rule hoare_seq_ext[OF _ thread_get_sp])
apply (rename_tac prio)
apply (rule_tac Q="is_schedulable_bool ct and
        ((\<lambda>s. is_schedulable_bool (cur_thread s) s) and
         (\<lambda>s. cur_thread s = ct)) and
        (\<lambda>s. scheduler_action s = switch_thread candidate) and
         (\<lambda>s. \<exists>d prio. ct \<in> set (ready_queues s d prio)) and
         K (ct \<noteq> it)" in hoare_weaken_pre[rotated])
apply (clarsimp ) subgoal sorry    (* need valid_idle *)
apply clarsimp
apply (rule hoare_seq_ext[OF _ thread_get_sp])
apply (rename_tac ct_prio)
apply (clarsimp simp: schedule_switch_thread_fastfail_def bind_assoc split del: if_split)
apply (rule hoare_seq_ext[OF _ gets_sp])
apply (rename_tac cdom)
apply (rule hoare_seq_ext[OF _ gets_sp])
apply (clarsimp simp: is_highest_prio_def bind_assoc split del: if_split)
apply (rename_tac highest_prio)
apply (rule_tac Q="obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_priority tcb = ct_prio)
             ct and
            (is_schedulable_bool ct and
             ((\<lambda>s. is_schedulable_bool (cur_thread s) s) and
              (\<lambda>s. cur_thread s = ct)) and
             (\<lambda>s. scheduler_action s = switch_thread candidate) and
             (\<lambda>s. \<exists>d prio. ct \<in> set (ready_queues s d prio))) and
            (\<lambda>s. cur_domain s = cdom) and
            (\<lambda>s. ( Max {prio. \<not> ready_queues s cdom prio = []} \<le> prio) =
                  highest_prio)" in hoare_weaken_pre[rotated])
apply clarsimp
apply (prop_tac "\<not> (\<forall>prio. ready_queues s (cur_domain s) prio = [])")
subgoal sorry (* need tcb_domain of cur_thread s is cur_domain s *)
apply fastforce

  apply wpsimp


  apply wpsimp

end


lemma schedule_ct_schedulable:
  "\<lbrace>ct_schedulable\<rbrace> Schedule_A.schedule \<lbrace>\<lambda>rv. ct_schedulable\<rbrace>"
  unfolding schedule_def
  apply (rule hoare_seq_ext[OF _ awaken_ct_schedulable])
  apply simp
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (rule hoare_seq_ext[OF _ is_schedulable_sp])
  apply (rule hoare_seq_ext[OF _ gets_sp])
  apply (case_tac action; simp add: bind_assoc)
  apply wpsimp
defer
  apply wpsimp

sorry

lemma schedule_ct_schedulable_or_idle:
  "\<lbrace>\<top>\<rbrace> Schedule_A.schedule \<lbrace>\<lambda>rv. ct_schedulable or ct_idle\<rbrace>"
  unfolding schedule_def
  apply wpsimp

sorry

lemma schedule_sa_resume[wp]:
  "\<lbrace>\<top>\<rbrace> Schedule_A.schedule \<lbrace>\<lambda>rv. sa_resume\<rbrace>"
sorry



(***)

lemma st_tcb_at_nostate_upd:
  "\<lbrakk> get_tcb t s = Some y; tcb_state y = tcb_state y' \<rbrakk> \<Longrightarrow>
  st_tcb_at P t' (s \<lparr>kheap := kheap s(t \<mapsto> TCB y')\<rparr>) = st_tcb_at P t' s"
  by (clarsimp simp add: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)

lemma pred_tcb_at_upd_apply:
  "pred_tcb_at proj P t (s\<lparr>kheap := p'\<rparr>) =
  pred_tcb_at proj P t (s\<lparr>kheap := (kheap s)(t := p' t)\<rparr>)"
  by (simp add: pred_tcb_at_def obj_at_def)

lemma thread_set_tcb_arch_is_schedulable_bool[wp]:
  "\<lbrace>\<lambda>s. is_schedulable_bool (cur_thread s) s\<rbrace>
     thread_set (\<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_context_set us (tcb_arch tcb)\<rparr>) t
   \<lbrace>\<lambda>rv s. is_schedulable_bool (cur_thread s) s\<rbrace>"
  apply (simp add: thread_set_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
  apply (wpsimp wp: set_object_wp)
  apply (fastforce simp: is_schedulable_bool_def is_sc_active_def get_tcb_def ko_atD
                         in_release_queue_def
                  split: option.splits )
  done

text \<open>The top-level invariance\<close>
thm activate_invs

lemma akernel_invs:
  "\<lbrace>\<lambda>s. invs s \<and> (e \<noteq> Interrupt \<longrightarrow> (ct_running s \<and> ct_schedulable s)) \<and>
        sa_resume s\<rbrace>
     (call_kernel e)
   \<lbrace>\<lambda>rv s. (invs s \<and> sa_resume s \<and> ((ct_running s \<and> ct_schedulable s) \<or> ct_idle s))\<rbrace>"
  unfolding call_kernel_def
  apply (wpsimp wp: activate_invs check_budget_invs charge_budget_invs is_schedulable_wp
                    update_time_stamp_invs hoare_drop_imps hoare_vcg_all_lift hoare_vcg_if_lift2)
  apply (rule_tac Q="\<lambda>_. ct_schedulable" in hoare_strengthen_post[rotated])
  apply blast
apply (wpsimp wp: charge_budget_invs is_schedulable_wp update_time_stamp_invs hoare_drop_imps
             hoare_vcg_all_lift hoare_vcg_if_lift2)+
  done

(*FIXME: should have (scheduler_action s = resume_cur_thread) as a postcondition*)
lemma kernel_entry_invs:
  "\<lbrace>\<lambda>s. invs s \<and> (e \<noteq> Interrupt \<longrightarrow> (ct_running s \<and> ct_schedulable s)) \<and>
       sa_resume s \<rbrace>
  (kernel_entry e us) :: (user_context,unit) s_monad
  \<lbrace>\<lambda>rv s. invs s \<and> sa_resume s \<and> ((ct_running s \<and> ct_schedulable s) \<or> ct_idle s)\<rbrace>"
  apply (simp add: kernel_entry_def)
  apply (wp akernel_invs thread_set_invs_trivial thread_set_ct_in_state select_wp
             static_imp_wp hoare_vcg_disj_lift
         | clarsimp simp add: tcb_cap_cases_def)+
  done

lemma device_update_invs:
  "\<lbrace>invs and (\<lambda>s. (dom ds) \<subseteq>  (device_region s))\<rbrace> do_machine_op (device_memory_update ds)
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: do_machine_op_def device_memory_update_def simpler_modify_def select_f_def
                   gets_def get_def bind_def valid_def return_def)
  apply (clarsimp simp: invs_def valid_state_def valid_irq_states_def valid_machine_state_def
                        cur_tcb_def pspace_respects_device_region_def cap_refs_respects_device_region_def
                  cong: user_mem_dom_cong
              simp del: split_paired_All)
  apply (clarsimp cong: device_mem_dom_cong simp:cap_range_respects_device_region_def
              simp del: split_paired_All split_paired_Ex)
  apply (intro conjI)
     apply fastforce
    apply fastforce
   apply (clarsimp simp del: split_paired_All split_paired_Ex)
   apply (drule_tac x = "(a,b)" in spec)
   apply (erule notE)
   apply (erule cte_wp_at_weakenE)
   apply clarsimp
   apply (fastforce split: if_splits) (* takes 20 secs *)
  apply (clarsimp simp: cur_sc_tcb_def)
  done

crunch device_state_inv[wp]: user_memory_update "\<lambda>ms. P (device_state ms)"

(* FIXME: move or delete *)
lemma dom_restrict_plus_eq:
  "a \<inter> b \<union> b = b"
  by auto

lemma user_memory_update[wp]:
  "\<lbrace>\<lambda>s. P (device_region s) \<rbrace> do_machine_op (user_memory_update a)
   \<lbrace>\<lambda>rv s. P (device_region s)\<rbrace>"
  by (simp add: do_machine_op_def user_memory_update_def simpler_modify_def
                valid_def bind_def gets_def return_def get_def select_f_def)

lemma do_user_op_invs:
  "\<lbrace>invs and ct_running\<rbrace>
   do_user_op f tc
   \<lbrace>\<lambda>_. invs and ct_running\<rbrace>"
  apply (simp add: do_user_op_def split_def)
  apply (wp device_update_invs)
  apply (wp select_wp dmo_invs | simp add:dom_restrict_plus_eq)+
  apply (clarsimp simp: user_memory_update_def simpler_modify_def
                        restrict_map_def invs_def cur_tcb_def
                 split: option.splits if_split_asm)
  apply (frule ptable_rights_imp_frame)
     apply fastforce+
  apply (clarsimp simp: valid_state_def device_frame_in_device_region)
  done

end
