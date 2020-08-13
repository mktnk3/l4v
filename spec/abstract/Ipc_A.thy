(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Specification of Inter-Process Communication.
*)

chapter "IPC"

theory Ipc_A
imports Tcb_A "./$L4V_ARCH/ArchFault_A"
begin

context begin interpretation Arch .

requalify_consts
  make_arch_fault_msg
  handle_arch_fault_reply
end

section \<open>Getting and setting the message info register.\<close>

definition
  get_message_info :: "obj_ref \<Rightarrow> (message_info,'z::state_ext) s_monad"
where
  "get_message_info thread \<equiv> do
     x \<leftarrow> as_user thread $ getRegister msg_info_register;
     return $ data_to_message_info x
   od"

section \<open>IPC Capability Transfers\<close>

definition
  remove_rights :: "cap_rights \<Rightarrow> cap \<Rightarrow> cap"
where
 "remove_rights rights cap \<equiv> cap_rights_update (cap_rights cap - rights) cap"

text \<open>In addition to the data payload a message may also contain capabilities.
When a thread requests additional capabilities be transferred the identities of
those capabilities are retreived from the thread's IPC buffer.\<close>
definition
  buffer_cptr_index :: nat
where
 "buffer_cptr_index \<equiv> (msg_max_length + 2)"

primrec
  get_extra_cptrs :: "obj_ref option \<Rightarrow> message_info \<Rightarrow> (cap_ref list,'z::state_ext) s_monad"
where
  "get_extra_cptrs (Some buf) mi =
    (liftM (map data_to_cptr) $ mapM (load_word_offs buf)
        [buffer_cptr_index ..< buffer_cptr_index + (unat (mi_extra_caps mi))])"
| "get_extra_cptrs None mi = return []"

definition
  get_extra_cptr :: "obj_ref \<Rightarrow> nat \<Rightarrow> (cap_ref,'z::state_ext) s_monad"
where
  "get_extra_cptr buffer n \<equiv> liftM data_to_cptr
      (load_word_offs buffer (n + buffer_cptr_index))"

text \<open>This function both looks up the addresses of the additional capabilities
and retreives them from the sender's CSpace.\<close>
definition
  lookup_extra_caps :: "obj_ref \<Rightarrow> data option \<Rightarrow> message_info \<Rightarrow> ((cap \<times> cslot_ptr) list,'z::state_ext) f_monad" where
  "lookup_extra_caps thread buffer mi \<equiv> doE
       cptrs \<leftarrow> liftE $ get_extra_cptrs buffer mi;
       mapME (\<lambda>cptr. cap_fault_on_failure (of_bl cptr) False $ lookup_cap_and_slot thread cptr) cptrs
  odE"

text \<open>Capability transfers. Capabilities passed along with a message are split
into two groups. Capabilities to the same endpoint as the message is passed
through are not copied. Their badges are unwrapped and stored in the receiver's
message buffer instead. Other capabilities are copied into the given slots.

Capability unwrapping allows a client to efficiently demonstrate to a server
that it possesses authority to two or more services that server provides.
\<close>
definition
  set_extra_badge :: "obj_ref \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_extra_badge buffer badge n \<equiv>
      store_word_offs buffer (buffer_cptr_index + n) badge"

type_synonym transfer_caps_data = "(cap \<times> cslot_ptr) list \<times> cslot_ptr list"

fun
  transfer_caps_loop :: "obj_ref option \<Rightarrow> obj_ref \<Rightarrow> nat
                          \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> cslot_ptr list
                          \<Rightarrow> message_info \<Rightarrow> (message_info,'z::state_ext) s_monad"
where
  "transfer_caps_loop ep rcv_buffer n [] slots
      mi = return (MI (mi_length mi) (of_nat n) (mi_caps_unwrapped mi)
                        (mi_label mi))"
| "transfer_caps_loop ep rcv_buffer n ((cap, slot) # morecaps)
         slots mi =
  const_on_failure (MI (mi_length mi) (of_nat n) (mi_caps_unwrapped mi)
                       (mi_label mi)) (doE
    transfer_rest \<leftarrow> returnOk $ transfer_caps_loop ep
         rcv_buffer (n + 1) morecaps;
    if is_ep_cap cap \<and> ep = Some (obj_ref_of cap)
    then doE
       liftE $ set_extra_badge rcv_buffer (cap_ep_badge cap) n;
       liftE $ transfer_rest slots (MI (mi_length mi) (mi_extra_caps mi)
         (mi_caps_unwrapped mi || (1 << n)) (mi_label mi))
    odE
    else if slots \<noteq> []
    then doE
      cap' \<leftarrow> derive_cap slot cap;
      whenE (cap' = NullCap) $ throwError undefined;
      liftE $ cap_insert cap' slot (hd slots);
      liftE $ transfer_rest (tl slots) mi
    odE
    else returnOk (MI (mi_length mi) (of_nat n) (mi_caps_unwrapped mi)
                       (mi_label mi))
  odE)"

definition
  transfer_caps :: "message_info \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
                   obj_ref option \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow>
                   (message_info,'z::state_ext) s_monad"
where
  "transfer_caps info caps endpoint receiver recv_buffer \<equiv> do
     dest_slots \<leftarrow> get_receive_slots receiver recv_buffer;
     mi' \<leftarrow> return $ MI (mi_length info) 0 0 (mi_label info);
     case recv_buffer of
       None \<Rightarrow> return mi'
     | Some receive_buffer \<Rightarrow>
         transfer_caps_loop endpoint receive_buffer 0 caps dest_slots mi'
   od"

section \<open>Fault Handling\<close>

text \<open>Threads fault when they attempt to access services that are not backed
by any resources. Such a thread is then blocked and a fault messages is sent to
its supervisor. When a reply to that message is sent the thread is reactivated.
\<close>

text \<open>Format a message for a given fault type.\<close>
fun
  make_fault_msg :: "fault \<Rightarrow> obj_ref \<Rightarrow> (data \<times> data list,'z::state_ext) s_monad"
where
  "make_fault_msg (CapFault cptr rp lf) thread = (do
     pc \<leftarrow> as_user thread getRestartPC;
     return (1, pc # cptr # (if rp then 1 else 0) # msg_from_lookup_failure lf)
   od)"
| "make_fault_msg (UnknownSyscallException n) thread = (do
     msg \<leftarrow> as_user thread $ mapM getRegister syscallMessage;
     return (2, msg @ [n])
   od)"
| "make_fault_msg (UserException exception code) thread = (do
     msg \<leftarrow> as_user thread $ mapM getRegister exceptionMessage;
     return (3, msg @ [exception, code])
   od)"
| "make_fault_msg (Timeout badge reason) thread = (do
     tcb \<leftarrow> gets_the $ get_tcb thread;
     case (tcb_sched_context tcb) of None \<Rightarrow> return (5, [badge])
     | Some sc \<Rightarrow> do
         consumed \<leftarrow> sched_context_update_consumed sc;
         return (5, badge # (ucast consumed) # [ucast (consumed >> 32)])
       od
   od)"
| "make_fault_msg (ArchFault af) thread = make_arch_fault_msg af thread " (* arch_fault *)

text \<open>React to a fault reply. The reply message is interpreted in a manner
that depends on the type of the original fault. For some fault types a thread
reconfiguration is performed. This is done entirely to save the fault message
recipient an additional system call. This function returns a boolean indicating
whether the thread should now be restarted.\<close>
fun
  handle_fault_reply :: "fault \<Rightarrow> obj_ref \<Rightarrow>
                         data \<Rightarrow> data list \<Rightarrow> (bool,'z::state_ext) s_monad"
where
  "handle_fault_reply (CapFault cptr rp lf) thread x y = return True"
| "handle_fault_reply (UnknownSyscallException n) thread label msg = do
     t \<leftarrow> arch_get_sanitise_register_info thread;
     as_user thread $ zipWithM_x
         (\<lambda>r v. setRegister r $ sanitise_register t r v)
         syscallMessage msg;
     return (label = 0)
   od"
| "handle_fault_reply (UserException exception code) thread label msg = do
     t \<leftarrow> arch_get_sanitise_register_info thread;
     as_user thread $ zipWithM_x
         (\<lambda>r v. setRegister r $ sanitise_register t r v)
         exceptionMessage msg;
     return (label = 0)
   od"
| "handle_fault_reply (Timeout badge reason) thread label msg = do
     t \<leftarrow> arch_get_sanitise_register_info thread;
     as_user thread $ zipWithM_x
         (\<lambda>r v. setRegister r $ sanitise_register t r v)
         timeoutMessage msg;
     return (label = 0)
   od"
| " handle_fault_reply (ArchFault af) thread label msg =
    handle_arch_fault_reply af thread label msg" (* arch_fault *)

text \<open>Transfer a fault message from a faulting thread to its supervisor.\<close>
definition
  do_fault_transfer :: "data \<Rightarrow> obj_ref \<Rightarrow> obj_ref
                             \<Rightarrow> obj_ref option \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "do_fault_transfer badge sender receiver buf \<equiv> do
    fault \<leftarrow> thread_get tcb_fault sender;
    f \<leftarrow> (case fault of
         Some f \<Rightarrow> return f
       | None \<Rightarrow> fail);
    (label, msg) \<leftarrow> make_fault_msg f sender;
    sent \<leftarrow> set_mrs receiver buf msg;
    set_message_info receiver $ MI sent 0 0 label;
    as_user receiver $ setRegister badge_register badge
  od"

section \<open>Synchronous Message Transfers\<close>

text \<open>Transfer a non-fault message.\<close>
definition
  do_normal_transfer :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> obj_ref option
                                    \<Rightarrow> data \<Rightarrow> bool \<Rightarrow> obj_ref
                                    \<Rightarrow> obj_ref option
                                    \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "do_normal_transfer sender sbuf endpoint badge grant
                     receiver rbuf  \<equiv>
  do
    mi \<leftarrow> get_message_info sender;
    caps \<leftarrow> if grant then lookup_extra_caps sender sbuf mi <catch> K (return [])
      else return [];
    mrs_transferred \<leftarrow> copy_mrs sender sbuf receiver rbuf (mi_length mi);
    mi' \<leftarrow> transfer_caps mi caps endpoint receiver rbuf;
    set_message_info receiver $ MI mrs_transferred (mi_extra_caps mi')
                                   (mi_caps_unwrapped mi') (mi_label mi);
    as_user receiver $ setRegister badge_register badge
  od"

text \<open>Transfer a message either involving a fault or not.\<close>
definition
  do_ipc_transfer :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow>
                       badge \<Rightarrow> bool \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "do_ipc_transfer sender ep badge grant
     receiver \<equiv> do

     recv_buffer \<leftarrow> lookup_ipc_buffer True receiver;
     fault \<leftarrow> thread_get tcb_fault sender;

     case fault
        of None \<Rightarrow> do
            send_buffer \<leftarrow> lookup_ipc_buffer False sender;
            do_normal_transfer sender send_buffer ep badge grant
                           receiver recv_buffer
            od
         | Some f \<Rightarrow> do_fault_transfer badge sender receiver recv_buffer
   od"

text \<open>Handle a message send operation performed on an endpoint by a thread.
If a receiver is waiting then transfer the message. If no receiver is available
and the thread is willing to block waiting to send then put it in the endpoint
sending queue.\<close>
definition
  send_ipc :: "bool \<Rightarrow> bool \<Rightarrow> badge \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool
                \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> (obj_ref option, 'z::state_ext) s_monad"
where
  "send_ipc block call badge can_grant can_grant_reply can_donate thread epptr \<equiv> do
     ep \<leftarrow> get_endpoint epptr;
     case (ep, block) of
         (IdleEP, True) \<Rightarrow> do
               set_thread_state thread (BlockedOnSend epptr
                                   \<lparr> sender_badge = badge,
                                     sender_can_grant = can_grant,
                                     sender_can_grant_reply = can_grant_reply,
                                     sender_is_call = call \<rparr>);
               set_endpoint epptr $ SendEP [thread];
               return None
             od
       | (SendEP queue, True) \<Rightarrow> do
               set_thread_state thread (BlockedOnSend epptr
                                   \<lparr> sender_badge = badge,
                                     sender_can_grant = can_grant,
                                     sender_can_grant_reply = can_grant_reply,
                                     sender_is_call = call\<rparr>);
               qs' \<leftarrow> sort_queue (queue @ [thread]);
               set_endpoint epptr $ SendEP qs';
               return None
             od
       | (IdleEP, False) \<Rightarrow> return None
       | (SendEP queue, False) \<Rightarrow> return None
       | (RecvEP (dest # queue), _) \<Rightarrow> do
                set_endpoint epptr $ (case queue of [] \<Rightarrow> IdleEP
                                                     | _ \<Rightarrow> RecvEP queue);
                recv_state \<leftarrow> get_thread_state dest;
                (reply, reply_can_grant) \<leftarrow> case recv_state
                  of (BlockedOnReceive _ reply data) \<Rightarrow> return (reply, receiver_can_grant data)
                  | _ \<Rightarrow> fail;
                do_ipc_transfer thread (Some epptr) badge can_grant dest;
                maybeM (reply_unlink_tcb dest) reply;
                sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context dest;

                fault \<leftarrow> thread_get tcb_fault thread;
                if call \<or> fault \<noteq> None then
                  if (can_grant \<or> reply_can_grant) \<and> reply \<noteq> None then
                    reply_push thread dest (the reply) can_donate
                  else
                    set_thread_state thread Inactive
                else when (can_donate \<and> sc_opt = None) $ do
                  thread_sc \<leftarrow> get_tcb_obj_ref tcb_sched_context thread;
                  sched_context_donate (the thread_sc) dest
                od;
\<comment> \<open>                new_sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context dest;
                test \<leftarrow> case new_sc_opt of Some scp \<Rightarrow> do
                            sufficient \<leftarrow> get_sc_refill_sufficient scp 0;
                            ready \<leftarrow> get_sc_refill_ready scp;
                            return (sufficient \<and> ready)
                        od
                        | _ \<Rightarrow> return True; \<comment> \<open>why does C allow dest to have no sc?\<close>
                assert test;\<close>
                set_thread_state dest Running;
                return (Some dest)
              od
       | (RecvEP [], _) \<Rightarrow> fail
   od"

text \<open>timeout fault handling needed for ensure_schedulable\<close>

definition valid_timeout_handler :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad" where
  "valid_timeout_handler tptr \<equiv> do
    tcb \<leftarrow> gets_the $ get_tcb tptr;
    if is_ep_cap (tcb_timeout_handler tcb)
    then do
      ep \<leftarrow> get_endpoint (cap_ep_ptr (tcb_timeout_handler tcb));
      case ep of
        RecvEP queue \<Rightarrow> do
          dest \<leftarrow> return $ hd queue; \<comment>\<open>queue should be non-empty\<close>
          sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context dest;
          case sc_opt of None \<Rightarrow> return False
                       | Some scp \<Rightarrow> do
                           active \<leftarrow> get_sc_active scp;
                           ready \<leftarrow> get_sc_refill_ready scp;
                           return (active \<and> ready)
                         od
          od
       | _ \<Rightarrow> return True
      od
    else return False
  od"

section \<open>Sending Fault Messages 1: handle_timeout\<close>

text \<open>When a thread encounters a fault, retreive its fault handler capability
and send a fault message.\<close>
definition
  send_fault_ipc :: "obj_ref \<Rightarrow> cap \<Rightarrow> fault \<Rightarrow> bool \<Rightarrow> (bool, 'z::state_ext) f_monad"
where
  "send_fault_ipc tptr handler_cap fault can_donate \<equiv>
     (case handler_cap
       of EndpointCap ref badge rights \<Rightarrow>
            liftE $ do
               thread_set (\<lambda>tcb. tcb \<lparr> tcb_fault := Some fault \<rparr>) tptr;
               unblocked \<leftarrow> send_ipc True False (cap_ep_badge handler_cap)
                        (AllowGrant \<in> rights) (AllowGrantReply \<in> rights) can_donate tptr
                        (cap_ep_ptr handler_cap);
               case unblocked of
                 Some tp \<Rightarrow> do
                   sched \<leftarrow> is_schedulable tp;
                   when sched $ possible_switch_to tp;
                   return True
                 od
               | None \<Rightarrow> return True
           od
        | NullCap \<Rightarrow> liftE $ return False
        | _ \<Rightarrow> fail)"

text \<open>timeout fault\<close>
definition handle_timeout :: "obj_ref \<Rightarrow> fault \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "handle_timeout tptr ex \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb tptr;
     assert (is_ep_cap (tcb_timeout_handler tcb));
     send_fault_ipc tptr (tcb_timeout_handler tcb) ex False;
     return ()
  od"


text \<open>If the thread has a valid timeout fault handler, deliver a fault with
  the given badge and reason.\<close>
definition
  maybe_timeout_fault :: "obj_ref \<Rightarrow> badge \<Rightarrow> reason \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "maybe_timeout_fault tptr badge reason \<equiv> do
    valid \<leftarrow> valid_timeout_handler tptr;
    if valid
    then handle_timeout tptr (Timeout badge reason)
    else
      when (reason = Exhausted) $ do
        sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context tptr;
        scp \<leftarrow> assert_opt sc_opt;
        active \<leftarrow> get_sc_active scp;
        assert active;
        postpone scp
     od
 od"

text \<open>Ensure that a thread can be placed in the scheduler with
  possibleSwitchTo, SCHED_ENQUEUE, or SCHED_APPEND. Faults the thread
  with a timeout fault or SC unbound fault if its SC would prevent it
  from being scheduled.

  If this returns true then the thread that was passed in is not
  modified and satisfies the preconditions of possibleSwitchTo.\<close>
definition
  ensure_schedulable :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad" where
  "ensure_schedulable tptr \<equiv> do
     ts \<leftarrow> get_thread_state tptr;
     assert (runnable ts);
     inq \<leftarrow> gets $ in_release_queue tptr;
     assert (\<not> inq);
     scopt \<leftarrow> get_tcb_obj_ref tcb_sched_context tptr;
     case scopt of
       None \<Rightarrow> do
         maybe_timeout_fault tptr 0 NoSC;
         return False
       od
     | Some scp \<Rightarrow> do
         active \<leftarrow> get_sc_active scp;
         sc \<leftarrow> get_sched_context scp;
         if \<not>active
         then do
           maybe_timeout_fault tptr (sc_badge sc) UnConfigured;
           return False
         od
         else do
           rr \<leftarrow> is_round_robin scp;
           ready \<leftarrow> get_sc_refill_ready scp;
           if \<not>rr \<and> \<not>ready
           then do
             maybe_timeout_fault tptr (sc_badge sc) Exhausted;
             return False
           od
           else return True
         od
       od
     od"

text \<open>Handle a message receive operation performed on an endpoint by a thread.
If a sender is waiting then transfer the message, otherwise put the thread in
the endpoint receiving queue.\<close>
definition
  isActive :: "notification \<Rightarrow> bool"
where
  "isActive ntfn \<equiv> case ntfn_obj ntfn
     of ActiveNtfn _ \<Rightarrow> True
      | _ \<Rightarrow> False"


text\<open>Helper function for performing \emph{signal} when receiving on a normal
endpoint\<close>
definition
  complete_signal :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "complete_signal ntfnptr tcb \<equiv> do
     ntfn \<leftarrow> get_notification ntfnptr;
     case ntfn_obj ntfn of
       ActiveNtfn badge \<Rightarrow> do
           as_user tcb $ setRegister badge_register badge;
           set_notification ntfnptr $ ntfn_obj_update (K IdleNtfn) ntfn
         od
     | _ \<Rightarrow> fail
   od"

definition
  do_nbrecv_failed_transfer :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "do_nbrecv_failed_transfer thread = do as_user thread $ setRegister badge_register 0; return () od"

definition is_timeout_fault :: "fault \<Rightarrow> bool" where
  "is_timeout_fault f \<equiv>
    (case f of Timeout _ _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition
  receive_ipc :: "obj_ref \<Rightarrow> cap \<Rightarrow> bool \<Rightarrow> cap \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "receive_ipc thread cap is_blocking reply_cap \<equiv> do
     (epptr,rights) \<leftarrow> (case cap
                       of EndpointCap ref badge rights \<Rightarrow> return (ref,rights)
                        | _ \<Rightarrow> fail);
     reply \<leftarrow> (case reply_cap of
                 ReplyCap r _ \<Rightarrow> do
                   tptr \<leftarrow> get_reply_obj_ref reply_tcb r;
                   when (tptr \<noteq> None \<and> the tptr \<noteq> thread) $ cancel_ipc (the tptr);
                   return (Some r)
                 od
               | NullCap \<Rightarrow> return None
               | _ \<Rightarrow> fail);
     ep \<leftarrow> get_endpoint epptr;
     ntfnptr \<leftarrow> get_tcb_obj_ref tcb_bound_notification thread;
     ntfn \<leftarrow> case_option (return default_notification) get_notification ntfnptr;
     if ntfnptr \<noteq> None \<and> isActive ntfn
     then
       complete_signal (the ntfnptr) thread
     else
       case ep
         of IdleEP \<Rightarrow> (case is_blocking of
              True \<Rightarrow> do
                  set_thread_state thread (BlockedOnReceive epptr reply \<lparr>receiver_can_grant = (AllowGrant \<in> rights)\<rparr>);
                  when (reply \<noteq> None) $
                    set_reply_obj_ref reply_tcb_update (the reply) (Some thread);
                  set_endpoint epptr (RecvEP [thread])
                od
              | False \<Rightarrow> do_nbrecv_failed_transfer thread)
            | RecvEP queue \<Rightarrow> (case is_blocking of
              True \<Rightarrow> do
                  set_thread_state thread (BlockedOnReceive epptr reply
                                                            \<lparr>receiver_can_grant = (AllowGrant \<in> rights)\<rparr>);
                  when (reply \<noteq> None) $ set_reply_obj_ref reply_tcb_update (the reply) (Some thread);
                  \<^cancel>\<open>FIXME RT: schedule_tcb?\<close>
                  qs' \<leftarrow> sort_queue (queue @ [thread]);
                  set_endpoint epptr (RecvEP qs')
                od
              | False \<Rightarrow> do_nbrecv_failed_transfer thread)
          | SendEP q \<Rightarrow> do
              assert (q \<noteq> []);
              queue \<leftarrow> return $ tl q;
              sender \<leftarrow> return $ hd q;
              set_endpoint epptr $
                (case queue of [] \<Rightarrow> IdleEP | _ \<Rightarrow> SendEP queue);
              sender_state \<leftarrow> get_thread_state sender;
              data \<leftarrow> (case sender_state
                       of BlockedOnSend ref data \<Rightarrow> return data
                        | _ \<Rightarrow> fail);
              do_ipc_transfer sender (Some epptr)
                        (sender_badge data) (sender_can_grant data)
                        thread;
              fault \<leftarrow> thread_get tcb_fault sender;
              if sender_is_call data \<or> fault \<noteq> None
              then
                if (sender_can_grant data \<or> sender_can_grant_reply data) \<and> reply \<noteq> None
                then do
                  sender_sc \<leftarrow> get_tcb_obj_ref tcb_sched_context sender;
                  donate \<leftarrow> return $ (sender_sc \<noteq> None) \<and> \<not>(case_option False is_timeout_fault fault);
                  reply_push sender thread (the reply) donate
                od
                else set_thread_state sender Inactive
              else do
                set_thread_state sender Running;
                sched \<leftarrow> ensure_schedulable sender;
                when sched $ possible_switch_to sender
              \<^cancel>\<open>FIXME RT: the C code has a test here for (refiil_sufficient sender'sc \<or> sender's sc is None)\<close>
              od
            od
   od"

section \<open>Asynchronous Message Transfers\<close>

text \<open>Helper function to handle a signal operation in the case
where a receiver is waiting.\<close>
definition
  update_waiting_ntfn :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref option \<Rightarrow> obj_ref option \<Rightarrow> badge \<Rightarrow>
                         (unit, 'z::state_ext) s_monad"
where
  "update_waiting_ntfn ntfnptr queue bound_tcb sc_ptr badge \<equiv> do
     assert (queue \<noteq> []);
     (dest,rest) \<leftarrow> return $ (hd queue, tl queue);
     set_notification ntfnptr $ \<lparr>
         ntfn_obj = (case rest of [] \<Rightarrow> IdleNtfn | _ \<Rightarrow> WaitingNtfn rest),
         ntfn_bound_tcb = bound_tcb,
         ntfn_sc = sc_ptr \<rparr>;
     set_thread_state dest Running;
     as_user dest $ setRegister badge_register badge;
     maybe_donate_sc dest ntfnptr;
     schedulable <- is_schedulable dest;
     when (schedulable) $ possible_switch_to dest
   od"

text \<open>Handle a message send operation performed on a notification object.
If a receiver is waiting then transfer the message, otherwise combine the new
message with whatever message is currently waiting.\<close>

(* helper function for checking if thread is blocked *)
definition
  receive_blocked :: "thread_state \<Rightarrow> bool"
where
  "receive_blocked st \<equiv> case st of
       BlockedOnReceive _ _ _ \<Rightarrow> True
     | _ \<Rightarrow> False"

definition
  send_signal :: "obj_ref \<Rightarrow> badge \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "send_signal ntfnptr badge \<equiv> do
    ntfn \<leftarrow> get_notification ntfnptr;
    case (ntfn_obj ntfn, ntfn_bound_tcb ntfn) of
          (IdleNtfn, Some tcb) \<Rightarrow> do
                  st \<leftarrow> get_thread_state tcb;
                  if receive_blocked st
                  then do
                      cancel_ipc tcb;
                      set_thread_state tcb Running;
                      as_user tcb $ setRegister badge_register badge;
                      maybe_donate_sc tcb ntfnptr;
                      schedulable <- is_schedulable tcb;
                      when (schedulable) $ possible_switch_to tcb
                    od
                  else set_notification ntfnptr $ ntfn_obj_update (K (ActiveNtfn badge)) ntfn
            od
       | (IdleNtfn, None) \<Rightarrow> set_notification ntfnptr $ ntfn_obj_update (K (ActiveNtfn badge)) ntfn
       | (WaitingNtfn queue, bound_tcb) \<Rightarrow> update_waiting_ntfn ntfnptr queue bound_tcb (ntfn_sc ntfn) badge
       | (ActiveNtfn badge', _) \<Rightarrow>
           set_notification ntfnptr $ ntfn_obj_update (K (ActiveNtfn (combine_ntfn_badges badge badge'))) ntfn
   od"


text \<open>Handle a receive operation performed on a notification object by a
thread. If a message is waiting then perform the transfer, otherwise put the
thread in the endpoint's receiving queue.\<close>
definition
  receive_signal :: "obj_ref \<Rightarrow> cap \<Rightarrow> bool \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
   "receive_signal thread cap is_blocking \<equiv> do
    ntfnptr \<leftarrow>
      case cap
        of NotificationCap ntfnptr badge rights \<Rightarrow> return ntfnptr
         | _ \<Rightarrow> fail;
    ntfn \<leftarrow> get_notification ntfnptr;
    case ntfn_obj ntfn
      of IdleNtfn \<Rightarrow>
                   (case is_blocking of
                     True \<Rightarrow> do
                          set_thread_state thread (BlockedOnNotification ntfnptr);
                          set_notification ntfnptr $ ntfn_obj_update (K (WaitingNtfn [thread])) ntfn;
                          maybe_return_sc ntfnptr thread;
                          schedule_tcb thread
                        od
                   | False \<Rightarrow> do_nbrecv_failed_transfer thread)
       | WaitingNtfn queue \<Rightarrow>
                   (case is_blocking of
                     True \<Rightarrow> do
                          set_thread_state thread (BlockedOnNotification ntfnptr);
                          qs' \<leftarrow> sort_queue (queue @ [thread]);
                          set_notification ntfnptr $ ntfn_obj_update (K (WaitingNtfn qs')) ntfn;
                          maybe_return_sc ntfnptr thread;
                          schedule_tcb thread
                        od
                   | False \<Rightarrow> do_nbrecv_failed_transfer thread)
       | ActiveNtfn badge \<Rightarrow> do
                     as_user thread $ setRegister badge_register badge;
                     set_notification ntfnptr $ ntfn_obj_update (K IdleNtfn) ntfn;
                     maybe_donate_sc thread ntfnptr
                   od
    od"

section \<open>Sending Fault Messages 2: handle_fault\<close>

text \<open>If a fault message cannot be sent then leave the thread inactive.\<close>
definition
  handle_no_fault :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "handle_no_fault tptr \<equiv> set_thread_state tptr Inactive"

text \<open>Handle a thread fault by sending a fault message if possible.\<close>
definition
  handle_fault :: "obj_ref \<Rightarrow> fault \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "handle_fault thread ex \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb thread;
     thread_sc \<leftarrow> get_tcb_obj_ref tcb_sched_context thread;
     has_fh \<leftarrow> send_fault_ipc thread (tcb_fault_handler tcb) ex (thread_sc \<noteq> None)
                    <catch> K (return False);
     unless has_fh $ (handle_no_fault thread);
     return ()
   od"

text \<open>Transfer a reply message and delete the one-use Reply capability.\<close>
definition
  do_reply_transfer :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> bool \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
 "do_reply_transfer sender reply grant \<equiv> do
    recv_opt \<leftarrow> get_reply_tcb reply;
    swp maybeM recv_opt (\<lambda>receiver. do
      state \<leftarrow> get_thread_state receiver;
      case state of
        BlockedOnReply r \<Rightarrow> do
          assert (r = reply);
          reply_remove receiver reply;
          fault \<leftarrow> thread_get tcb_fault receiver;
          case fault of
            None \<Rightarrow> do
              do_ipc_transfer sender None 0 grant receiver;
              set_thread_state receiver Running
            od
          | Some f \<Rightarrow> do
              mi \<leftarrow> get_message_info sender;
              buf \<leftarrow> lookup_ipc_buffer False sender;
              mrs \<leftarrow> get_mrs sender buf mi;
              restart \<leftarrow> handle_fault_reply f receiver (mi_label mi) mrs;
              thread_set (\<lambda>tcb. tcb \<lparr> tcb_fault := None \<rparr>) receiver;
              set_thread_state receiver (if restart then Restart else Inactive)
            od;

          state \<leftarrow> get_thread_state receiver;
          sched <- ensure_schedulable receiver;
          when (runnable (state) \<and> sched) $
             possible_switch_to receiver
        od
      | _ \<Rightarrow> return ()
    od)
  od"

text \<open>This function transfers a reply message to a thread when that message
is generated by a kernel service.\<close>
definition
  reply_from_kernel :: "obj_ref \<Rightarrow> (data \<times> data list) \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "reply_from_kernel thread x \<equiv> do
    (label, msg) \<leftarrow> return x;
    buf \<leftarrow> lookup_ipc_buffer True thread;
    as_user thread $ setRegister badge_register 0;
    len \<leftarrow> set_mrs thread buf msg;
    set_message_info thread $ MI len 0 0 label
  od"


(* below are moved from Schedule_A, due to a dependency issue *)

definition
  end_timeslice :: "bool \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "end_timeslice canTimeout = do
     ct \<leftarrow> gets cur_thread;
     sc_ptr \<leftarrow> gets cur_sc;
     csc \<leftarrow> get_sched_context sc_ptr;
     curtime \<leftarrow> gets cur_time;
     tcb \<leftarrow> gets_the $ get_tcb ct;

     if canTimeout \<and> (is_ep_cap (tcb_timeout_handler tcb)) then
       handle_timeout ct (Timeout (sc_badge csc) Exhausted)
     else if sc_refill_ready curtime csc \<and> sc_refill_sufficient 0 csc then do
     \<comment> \<open>C code assets @{text cur_thread} not to be in ready q at this point\<close>
       d \<leftarrow> thread_get tcb_domain ct;
       prio \<leftarrow> thread_get tcb_priority ct;
       queue \<leftarrow> get_tcb_queue d prio;
       assert (\<not>(ct \<in> set queue));
       tcb_sched_action tcb_sched_append ct \<comment> \<open>@{text \<open>not_queued & ready & sufficient & runnable\<close>}\<close>
     od
     else
       postpone sc_ptr
  od"

definition
  charge_budget :: "ticks \<Rightarrow> bool \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "charge_budget consumed canTimeout = do
    csc_ptr \<leftarrow> gets cur_sc;
    csc \<leftarrow> get_sched_context csc_ptr;
    robin \<leftarrow> is_round_robin csc_ptr;
    if robin then refill_budget_check_round_robin consumed
    else refill_budget_check consumed;
    update_sched_context csc_ptr (\<lambda>sc. sc\<lparr>sc_consumed := (sc_consumed sc) + consumed \<rparr>);
    modify $ consumed_time_update (K 0);
    ct \<leftarrow> gets cur_thread;
    sched \<leftarrow> is_schedulable ct;
    when (sched) $ do
      sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context ct;
      assert (sc_opt = (Some csc_ptr));
      end_timeslice canTimeout;
      reschedule_required;
      modify (\<lambda>s. s\<lparr>reprogram_timer := True\<rparr>)
    od
  od"

definition
  check_budget :: "(bool, 'z::state_ext) s_monad"
where
  "check_budget = do
     csc \<leftarrow> gets cur_sc;
     consumed \<leftarrow> gets consumed_time;
     sc \<leftarrow> get_sched_context csc;
    \<comment> \<open>FIXME RT: maybe assert @{text refill_ready}?\<close>
     capacity \<leftarrow> get_sc_refill_capacity csc consumed;

     full \<leftarrow> return (size (sc_refills sc) = sc_refill_max sc); \<comment> \<open>@{text \<open>= refill_full csc\<close>}\<close>

     robin \<leftarrow> return (sc_period sc = sc_budget sc);

     if capacity \<ge> MIN_BUDGET \<and> (robin \<or> \<not>full) then do
       dom_exp \<leftarrow> gets is_cur_domain_expired;
       if dom_exp then do
         modify (\<lambda>s. s\<lparr> reprogram_timer := True \<rparr>);
         reschedule_required;
         return False
      od
      else return True
    od
    else do
      consumed \<leftarrow> gets consumed_time;
      charge_budget consumed True;
      return False
    od
  od"

definition
  check_budget_restart :: "(bool, 'z::state_ext) s_monad"
where
  "check_budget_restart = do
     result \<leftarrow> check_budget;
    cur \<leftarrow> gets cur_thread;
    st \<leftarrow> get_thread_state cur;
    when (\<not>result \<and> runnable st) $ set_thread_state cur Restart;
    return result
  od"

text \<open> The Scheduling Control invocation configures the budget of a scheduling context. \<close>
definition
  invoke_sched_control_configure :: "sched_control_invocation \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "invoke_sched_control_configure iv \<equiv>
  case iv of InvokeSchedControlConfigure sc_ptr budget period mrefills badge \<Rightarrow> do
    sc \<leftarrow> get_sched_context sc_ptr;
    set_sc_obj_ref sc_badge_update sc_ptr badge;

    when (sc_tcb sc \<noteq> None) $ do
      tcb_ptr \<leftarrow> assert_opt $ sc_tcb sc;
      tcb_release_remove tcb_ptr;
      tcb_sched_action tcb_sched_dequeue tcb_ptr;
      cur_sc \<leftarrow> gets cur_sc;
      when (cur_sc = sc_ptr) $ commit_time
           \<comment> \<open>The C code here includes an assert saying that @{text check_budget} returns True.
               However, we can call @{text invoke_sched_control_configure} only if the call to
               @{text check_budget_restart} at the beginning of @{text handle_event} returns True, so we
               know that @{text check_budget} would return True if called here.\<close>
    od;

    (period, mrefills) \<leftarrow> return (if period = budget then (0, MIN_REFILLS) else (period, mrefills));

    if 0 < sc_refill_max sc \<and> sc_tcb sc \<noteq> None
    then do tcb_ptr \<leftarrow> assert_opt $ sc_tcb sc;
            st \<leftarrow> get_thread_state tcb_ptr;
            if runnable st
            then refill_update sc_ptr period budget mrefills
            else refill_new sc_ptr mrefills budget period
         od
    else refill_new sc_ptr mrefills budget period;

    when (sc_tcb sc \<noteq> None) $ do
      tcb_ptr \<leftarrow> assert_opt $ sc_tcb sc;
      st \<leftarrow> get_thread_state tcb_ptr;
      sched_context_resume sc_ptr;
      ct \<leftarrow> gets cur_thread;
      if tcb_ptr = ct then reschedule_required
      else when (runnable st) $ possible_switch_to tcb_ptr
    od
  od"


text \<open>moved from IpcCance_A due to ensure_schedulable dependency\<close>

definition
  restart_thread_if_no_fault :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "restart_thread_if_no_fault t \<equiv> do
     fault \<leftarrow> thread_get tcb_fault t;
     if fault = None
     then do
       set_thread_state t Restart;
       sched \<leftarrow> ensure_schedulable t;
       when sched $ possible_switch_to t
     od
     else set_thread_state t Inactive
   od"

text \<open>The badge stored by thread waiting on a message send operation.\<close>
primrec (nonexhaustive)
  blocking_ipc_badge :: "thread_state \<Rightarrow> badge"
where
  "blocking_ipc_badge (BlockedOnSend t payload) = sender_badge payload"

text \<open>Cancel all message send operations on threads queued in this endpoint
and using a particular badge.\<close>
definition
  cancel_badged_sends :: "obj_ref \<Rightarrow> badge \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "cancel_badged_sends epptr badge \<equiv> do
    ep \<leftarrow> get_endpoint epptr;
    case ep of
          IdleEP \<Rightarrow> return ()
        | RecvEP _ \<Rightarrow>  return ()
        | SendEP queue \<Rightarrow>  do
            set_endpoint epptr IdleEP;
            queue' \<leftarrow> (swp filterM queue) (\<lambda> t. do
                st \<leftarrow> get_thread_state t;
                if blocking_ipc_badge st = badge then do
                  restart_thread_if_no_fault t;
                  return False
                od
                else return True
            od);
            ep' \<leftarrow> return (case queue' of
                           [] \<Rightarrow> IdleEP
                         | _ \<Rightarrow> SendEP queue');
            set_endpoint epptr ep';
            reschedule_required
        od
  od"

text \<open>
  Unbind a TCB from its scheduling context. If the TCB is runnable,
  remove from the scheduler.
\<close>
definition
  sched_context_unbind_tcb_can_timeout :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_unbind_tcb_can_timeout sc_ptr = do
     sc \<leftarrow> get_sched_context sc_ptr;
     tptr \<leftarrow> assert_opt $ sc_tcb sc;
     cur \<leftarrow> gets $ cur_thread;
     when (tptr = cur) $ reschedule_required;
     tcb_sched_action tcb_sched_dequeue tptr;
     tcb_release_remove tptr;
     st \<leftarrow> get_thread_state tptr;
     when (runnable st) $ maybe_timeout_fault tptr 0 NoSC;
     set_tcb_obj_ref tcb_sched_context_update tptr None;
     set_sc_obj_ref sc_tcb_update sc_ptr None
  od"

text \<open>
  Unbind a TCB from its scheduling context.
  Takes the TCB as argument and calls @{text sched_context_unbind_tcb}.
\<close>
definition
  maybe_sched_context_unbind_tcb_can_timeout :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "maybe_sched_context_unbind_tcb_can_timeout target = do
     sc_ptr_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context target;
     maybeM sched_context_unbind_tcb_can_timeout sc_ptr_opt
  od"

text \<open> Unbind TCB, if there is one bound. \<close>
definition
  sched_context_unbind_all_tcbs_can_timeout :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_unbind_all_tcbs_can_timeout sc_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    when (sc_tcb sc \<noteq> None \<and> sc_ptr \<noteq> idle_sc_ptr) $ sched_context_unbind_tcb_can_timeout sc_ptr
  od"


text \<open>moved from SchedContext_A due to ensure_schedulable dependency\<close>

text \<open>  Bind a TCB to a scheduling context. \<close>

definition
  test_possible_switch_to :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "test_possible_switch_to tcb_ptr = do
    sched \<leftarrow> ensure_schedulable tcb_ptr;
    when sched $ possible_switch_to tcb_ptr
  od"

definition
  sched_context_bind_tcb :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_bind_tcb sc_ptr tcb_ptr = do
    set_sc_obj_ref sc_tcb_update sc_ptr (Some tcb_ptr);
    set_tcb_obj_ref tcb_sched_context_update tcb_ptr (Some sc_ptr);
    sched_context_resume sc_ptr;
    sched <- ensure_schedulable tcb_ptr;
    when sched $ do
      tcb_sched_action tcb_sched_enqueue tcb_ptr;
      reschedule_required
      od
  od"

definition
  maybe_sched_context_bind_tcb :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "maybe_sched_context_bind_tcb sc_ptr tcb_ptr = do
     sc' \<leftarrow> get_tcb_obj_ref tcb_sched_context tcb_ptr;
     when (sc' \<noteq> Some sc_ptr) $ sched_context_bind_tcb sc_ptr tcb_ptr
   od"

text \<open>moved from Tcb_A due to ensure_schedulable dependency\<close>

text \<open>Reactivate a thread if it is not already running.\<close>
definition
  restart :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad" where
 "restart thread \<equiv> do
    state \<leftarrow> get_thread_state thread;
    sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context thread;
    when (\<not> runnable state \<and> \<not> idle state) $ do
      cancel_ipc thread;
      set_thread_state thread Restart;
      maybeM sched_context_resume sc_opt;
      test_possible_switch_to thread
    od
  od"

text \<open>TCB capabilities confer authority to perform seven actions. A thread can
request to yield its timeslice to another, to suspend or resume another, to
reconfigure another thread, or to copy register sets into, out of or between
other threads.\<close>
fun
  invoke_tcb :: "tcb_invocation \<Rightarrow> (data list, 'z::state_ext) p_monad"
where
  "invoke_tcb (Suspend thread) = liftE (do suspend thread; return [] od)"
| "invoke_tcb (Resume thread) = liftE (do restart thread; return [] od)"

| "invoke_tcb (ThreadControlCaps target slot fault_handler timeout_handler croot vroot buffer)
   = doE
    install_tcb_cap target slot 3 fault_handler;
    install_tcb_cap target slot 4 timeout_handler;
    install_tcb_cap target slot 0 croot;
    install_tcb_cap target slot 1 vroot;
    install_tcb_frame_cap target slot buffer;
    returnOk []
  odE"

| "invoke_tcb (ThreadControlSched target slot fault_handler mcp priority sc)
   = doE
    install_tcb_cap target slot 3 fault_handler;
    liftE $ maybeM (\<lambda>(newmcp, _). set_mcpriority target newmcp) mcp;
    liftE $ maybeM (\<lambda>(prio, _). set_priority target prio) priority;
    liftE $ maybeM (\<lambda>scopt. case scopt of
                              None \<Rightarrow> maybe_sched_context_unbind_tcb_can_timeout target
                            | Some sc_ptr \<Rightarrow> maybe_sched_context_bind_tcb sc_ptr target) sc;
    returnOk []
  odE"

| "invoke_tcb (CopyRegisters dest src suspend_source resume_target transfer_frame transfer_integer transfer_arch) =
  (liftE $ do
    when suspend_source $ suspend src;
    when resume_target $ restart dest;
    when transfer_frame $ do
        mapM_x (\<lambda>r. do
                v \<leftarrow> as_user src $ getRegister r;
                as_user dest $ setRegister r v
        od) frame_registers;
        pc \<leftarrow> as_user dest getRestartPC;
        as_user dest $ setNextPC pc
    od;
    when transfer_integer $
        mapM_x (\<lambda>r. do
                v \<leftarrow> as_user src $ getRegister r;
                as_user dest $ setRegister r v
        od) gpRegisters;
    cur \<leftarrow> gets cur_thread;
    arch_post_modify_registers cur dest;
    when (dest = cur) reschedule_required;
    return []
  od)"

| "invoke_tcb (ReadRegisters src suspend_source n arch) =
  (liftE $ do
    when suspend_source $ suspend src;
    self \<leftarrow> gets cur_thread;
    regs \<leftarrow> return (take (unat n) $ frame_registers @ gp_registers);
    as_user src $ mapM getRegister regs
  od)"

| "invoke_tcb (WriteRegisters dest resume_target values arch) =
  (liftE $ do
    self \<leftarrow> gets cur_thread;
    b \<leftarrow> arch_get_sanitise_register_info dest;
    as_user dest $ do
        zipWithM (\<lambda>r v. setRegister r (sanitise_register b r v))
            (frameRegisters @ gpRegisters) values;
        pc \<leftarrow> getRestartPC;
        setNextPC pc
    od;
    arch_post_modify_registers self dest;
    when resume_target $ restart dest;
    when (dest = self) reschedule_required;
    return []
  od)"

| "invoke_tcb (NotificationControl tcb (Some ntfnptr)) =
  (liftE $ do
    bind_notification tcb ntfnptr;
    return []
  od)"

| "invoke_tcb (NotificationControl tcb None) =
  (liftE $ do
    unbind_notification tcb;
    return []
  od)"

| "invoke_tcb (SetTLSBase tcb tls_base) =
  (liftE $ do
    as_user tcb $ setRegister tlsBaseRegister tls_base;
    cur \<leftarrow> gets cur_thread;
    when (tcb = cur) reschedule_required;
    return []
  od)"


text \<open>moved from Schedule_A due to ensure_schedulable dependency\<close>

definition
  invoke_sched_context :: "sched_context_invocation \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "invoke_sched_context iv \<equiv> case iv of
    InvokeSchedContextConsumed sc_ptr args \<Rightarrow> set_consumed sc_ptr args
  | InvokeSchedContextBind sc_ptr cap \<Rightarrow> (case cap of
      ThreadCap tcb_ptr \<Rightarrow> sched_context_bind_tcb sc_ptr tcb_ptr
    | NotificationCap ntfn _ _ \<Rightarrow> sched_context_bind_ntfn sc_ptr ntfn
    | _ \<Rightarrow> fail)
  | InvokeSchedContextUnbindObject sc_ptr cap \<Rightarrow> (case cap of
      ThreadCap _ \<Rightarrow> sched_context_unbind_tcb_can_timeout sc_ptr
    | NotificationCap _ _ _ \<Rightarrow> sched_context_unbind_ntfn sc_ptr
    | _ \<Rightarrow> fail)
  | InvokeSchedContextUnbind sc_ptr cap \<Rightarrow> do
      sched_context_unbind_all_tcbs_can_timeout sc_ptr;
      sched_context_unbind_ntfn sc_ptr;
      sched_context_unbind_reply sc_ptr
    od
  | InvokeSchedContextYieldTo sc_ptr args \<Rightarrow>
      sched_context_yield_to sc_ptr args"


text \<open>moved from CSpace_A due to ensure_schedulable dependency\<close>

section \<open>Invoking CNode capabilities\<close>

text \<open>The CNode capability confers authority to various methods
which act on CNodes and the capabilities within them. Copies of
capabilities may be inserted in empty CNode slots by
Insert. Capabilities may be moved to empty slots with Move or swapped
with others in a three way rotate by Rotate. A Reply capability stored
in a thread's last-caller slot may be saved into a regular CNode slot
with Save.  The Revoke, Delete and Recycle methods may also be
invoked on the capabilities stored in the CNode.\<close>

definition
  invoke_cnode :: "cnode_invocation \<Rightarrow> (unit, 'z::state_ext) p_monad" where
  "invoke_cnode i \<equiv> case i of
    RevokeCall dest_slot \<Rightarrow> cap_revoke dest_slot
  | DeleteCall dest_slot \<Rightarrow> cap_delete dest_slot
  | InsertCall cap src_slot dest_slot \<Rightarrow>
       without_preemption $ cap_insert cap src_slot dest_slot
  | MoveCall cap src_slot dest_slot \<Rightarrow>
       without_preemption $ cap_move cap src_slot dest_slot
  | RotateCall cap1 cap2 slot1 slot2 slot3 \<Rightarrow>
       without_preemption $
       if slot1 = slot3 then
         cap_swap cap1 slot1 cap2 slot2
       else
         do cap_move cap2 slot2 slot3; cap_move cap1 slot1 slot2 od
  | CancelBadgedSendsCall (EndpointCap ep b R) \<Rightarrow>
    without_preemption $ when (b \<noteq> 0) $ cancel_badged_sends ep b
  | CancelBadgedSendsCall _ \<Rightarrow> fail"


end
