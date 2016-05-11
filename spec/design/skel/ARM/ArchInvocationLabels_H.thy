(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Architecture-specific Invocation Labels"

theory ArchInvocationLabels_H
imports "../../../lib/Enumeration" "../../machine/ARM/Setup_Locale"
begin
context Arch begin global_naming ARM_H

text {*
  An enumeration of arch-specific system call labels.
*}

#INCLUDE_HASKELL SEL4/API/InvocationLabels/ARM.lhs CONTEXT ARM_H ONLY ArchInvocationLabel

end

context begin interpretation Arch .
requalify_types arch_invocation_label
end

context Arch begin global_naming ARM_H

#INCLUDE_HASKELL SEL4/API/InvocationLabels/ARM.lhs CONTEXT ARM_H instanceproofs ONLY ArchInvocationLabel

end
end
