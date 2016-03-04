(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchBits_AI
imports "../Invariants_AI"
begin

context ARM begin

lemma invs_unique_table_caps[elim!]:
  "invs s \<Longrightarrow> unique_table_caps (arch_caps_of (caps_of_state s))"
  by (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)

lemma invs_unique_refs[elim!]:
  "invs s \<Longrightarrow> unique_table_refs (arch_caps_of (caps_of_state s))"
  by (simp add: invs_def valid_state_def valid_arch_caps_def)


lemma invs_pd_caps:
  "invs s \<Longrightarrow> valid_table_caps s"
  by (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)

lemma invs_valid_vs_lookup[elim!]:
  "invs s \<Longrightarrow> valid_vs_lookup s "
  by (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)

lemma pbfs_atleast_pageBits:
  "pageBits \<le> pageBitsForSize sz"
  by (cases sz) (auto simp: pageBits_def)

end

end