(*|
.. coq:: none
|*)

Require Import FjfjParsing.
Require Import LangFjfj2.
Require Import Indexification.
Require Import Lia.
Require Import NArith.
Require Import List.

Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.


Import ListNotations.
Require RfSpec.
Open Scope N.
Require Import Tactics.

Require Import egg.Loader.
(*|
.. coq:: none 
|*)
Local Instance rf_submodules : instances := 
#| 
    reg.mkReg r0;
    reg.mkReg r1;
    reg.mkReg r2;
    reg.mkReg r3
|#.

Definition write_rf :=
  (action_method (idx val)
    (begin 
      (if (< idx 4)
        pass
        abort)
      (if (= idx 0)
        {write r0 val} 
        pass)
      (if (= idx 1)
        {write r1 val} 
        pass)
      (if (= idx 2)
        {write r2 val} 
        pass)
      (if (= idx 3)
        {write r3 val} 
        pass))).
Arguments write_rf /.
        
Definition read_rf :=
  (value_method (idx)
    (begin 
      (if (< idx 4)
        pass
        abort)
      (set res 0)
      (if (= idx 0)
        (set res {read r0})
        pass)
      (if (= idx 1)
        (set res {read r1})
        pass)
      (if (= idx 2)
        (set res {read r2})
        pass)
      (if (= idx 3)
        (set res {read r3})
        pass)
      res)).
Arguments read_rf /.
    
Global Instance mkRf4 : module _ := 
    module#(vmet [ read_rf ] amet [ write_rf ]).

(*|
.. raw:: latex

  \paragraph{1. Picking a simulation relation candidate $\phi$}
  In this case, let's pick

.. coq:: unfold 
|*)
Definition ϕ (ist : SModule) (sst : SModule) := 
    exists (rfs: N -> N) (r0 r1 r2 r3 : N), 
        sst = *( rfs )* /\
        ist = *[| r0; r1; r2; r3 |]* /\
        rfs 0 = r0 /\ rfs 1 = r1 /\ rfs 2 = r2 /\ rfs 3 = r3.
(*|
.. coq:: none 
|*)
Arguments ϕ / ist sst.
Arguments RfSpec.read'  rf idx /.
Notation mkRfSpec := RfSpec.mkRf.
Arguments mkRfSpec /.
Notation "a '<|' b" := (indistinguishable (spec_of mkRf4)  (spec_of mkRfSpec) a b) (at level 20, only parsing).
Notation " '('  a '<|' b ')' " := (indistinguishable _  _ a b) (at level 20, only printing).
Notation " '(' a  '→*'  b ')' " := (existSR _ a b) (at level 20, only printing).
Close Scope string_scope.

(*|
.. raw:: latex

  %\remark
  {Let's remember that \verb|*( something )*| stands for the state of a \emph{primitive} module that would contain \verb|something|.
  (That is to not be confused with \verb|(* this is a comment *)|).
  Let's also introduce a related notation for the state of \emph{nonprimitive} modules.
  The state of a \emph{nonprimitive} is made of several substates (one per submodule), for example, we note \verb=*[| a; b; c |]*= for a module state containing 3 submodules which are containing \verb|a|, \verb|b| and verb|c|.
  Sometimes we have a hierarchy of states so we end up writing  \verb=*[| a; [| e;f |]; c |]*= to say that the second submodule is itself a nonprimitive module that contains two primitive modules containing \verb|e| and \verb|f|.
  }

  This $\phi$ reads as: the specification state is of the shape of a primitive state that contains a function $\mathit{rfs}$ from $\mathbb{N}$ to $\mathbb{N}$,
  the implementation state is of the shape of a nonprimitive module state composed of 4 primitive submodule states $r0,r1,r2$, and $r3$, such that
  the function $\mathit{rfs}$ is equal to $r_i$ when its argument is $i$, i.e. the specification register file contains in its first 4 registers the same value as the 4 implementation registers.

  \paragraph{2. Showing that $\phi\; i\; s$ implies $i \prec s$}
  The most difficult part of that proof is to understand the simple statement we are trying to prove.
  We have to prove that for any state of register files that are related by $\phi$, reading in the implementation register file would return a value that would be the same as reading the specification register file.
  There is a small subtlety: the implementation register file has only 4 registers, while the specification register file has infinitely many of them.
  So how can that property be true?
  The trick is the \emph{guard} on the implementation register file: one can never read the implementation register file at any index higher or equal to 4.
  Hence, if we assume that we successfully read the implementation register, necessarily the index was smaller than 4.

  Now that the reader understands why the property is true and intuitively trivial, let's elaborate step-by-step on this easy proof to explain how we carry out the proof in the proof assistant.

  Indeed, as the reader might already know, even elementary properties can sometimes require a disproportionate amount of effort to prove.
  To avoid this potentially demoralizing fact, one solution is to build a set of \emph{tactics} (or proof-script automations) that are hopefully able to handle those easy facts. So we have to provide suitable base tactics to make the proof assistant able to discharge proof obligations automatically, hopefully as fast as a standard human can prove reasonably obvious facts.


.. coq:: fold 
|*)
Lemma ϕ_implies_state_simul:
  forall ist sst, ϕ ist sst -> ist <| sst. (* .in *)  
  (* We start the proof by using our tactic "prove_state_simulation"
  that will generate all the proof obligations corresponding to the
  definition of "ist state is simulating sst". *)
  prove_state_simulation. (* .in *)
  { (* .in *)
    (* The first goal corresponds to proving that if we 
    assume that we successfully call the [read_rf] method at an index 
    [arg] from the implementation register file (hypothesis named HB)
    then we can prove (statement below the line) that we can call the
    [read] method of the specification register file at index [arg],
    and we will obtain the same value.

    One can check that what is below the line is exactly the definition 
    of the [read] value method of the specification register
    file returning [ret_valu]e: it is exactly the predicate we defined
    for the semantics of the [read] value method when we defined this spec. *) (* .in *) 
    idtac. (* .no-in .unfold -.h#* .h#HB  *)
    (* We can use our symbolic-evaluation tactic to tackle this goal.
    Our tactic, from the hypothesis HB, deduces that there are 5 
    possible "program paths" in which the semantics judgment 
    saying that the [read_rf] value method was successfully called
    can be derived. 

    4 cases are very similar (corresponding to [arg] = 0, 1, 2 or 3), and 
    the last case ([arg] >= 4) is actually absurd, as we will see 
    in a minute.
    
    Let's display one of the 4 first cases that we made Coq generate 
    for us just after the call to our symb_ex_split tactic: *)
    symb_ex_split. (* .unfold -.h#* .h#Heqb2 .h#Heqb0 .h#Heqb1 .h#HA0 -.g#* .g#1 *)
    (* We can see that the tactic records all the hypotheses it accumulated 
    when symbolically running this program. 
    In this case, the case shown is for [arg] = 3, so we have in 
    the context the facts that the semantics passed on the false branch 
    of [arg] not being equal to any of 0,1 or 2, and 
    the fact that 3 is smaller than 4 (the first branch).

    Note that the tactic also simplified the goal, replacing [arg]
    in the goal by 3 (as in this case [arg] = 3) and replaced [ret_value]
    by [rfs 3], as expected from a little symbolic evaluator.

    Looking at the goal, it is trivial, and indeed is proven
    easily by Coq automation (and the same for the other similar 
    3 cases), by the following tactic: *)
    all: eauto. (* .in *)
    (* 
      Only one case is left: the case [arg] >= 4.
      This case is interesting because we can see a set of hypotheses
      that is contradictory: no number is simultaneously smaller 
      than 4 and neither 0, 1, 2 or 3. 
      We use a little tactic to solve this kind of arithmetic goals: 
    *)
    idtac. (* .no-in .unfold -.h#* .h#Heqb .h#Heqb2 .h#Heqb0 .h#Heqb1 .h#HA0 *)
    arithmetic_hammer.
  } (* .in *)
  (* We are done with the first proof obligation. *)
  { (* .in *)
    (* The second case is absolutely trivial; it requires us to prove that 
    if we assume that we can successfully call the [write_rf] action method 
    of the implementation register file, then we can necessarily call the
    [write_rf] action method of the specification register file:
    in Bluespec terms, the guard is ready.
    
    As the [write_rf] action method of the specification register file can 
    always be called, this obligation is trivial, and we don't bother
    to show it.  *)
    eauto. (* .in *)
  }(* .in *)
  (* We don't have any subgoals left, and we can declare the proof finished: *)
  Qed.

(*|
.. raw:: latex

  Now is a good time to go back on an important principle of our approach to
  verification (that we mentioned in the introduction).  
  Our framework (and more
  generally Coq), in contrast to standard model-checking frameworks, is not
  designed to perform very large case analysis.
  In the world of SMT solvers and model checkers, it is common to have the
  computer doing bit-blasting on dozens of bits, effectively doing case analysis
  over millions of cases in seconds.  This bulldozer technique works well enough
  for those approaches but does not for us. 
  
  Our case-analysis techniques are much more modest.
  Our rule of thumb is never  to attempt a proof strategy that would require more than a hundred cases.
  In practice this works well, because as we explained in the introduction, our philosophy is to consider proofs that are mimicking what we think about in our brains when considering the correctness of a design, and those can physically never involve too many cases.
  Even for our just-presented example, this little proof of a register file could also have been carried out without these 5 case splits. 
  % This is left as an exercise to the reader, but with just 2 cases for example.


  % In our methodology, we both don't want to and cannot analyze that many cases.
  % First we don't want to, because our intention is to do proofs that are directly representing the reason why the human architect thinks their design is correct, and the human architect never think about a million different cases.
  % Second, we cannot, because performance-wise due to the way terms are represented, and due to the way tactics are executed, and the cost of primitive coq tactics, the order of magnitude for handling a single case will often be between 0.01 and 1 second when the case is difficult to handle. 
  % This directly precludes analyzing millions of cases.
  \paragraph{3. Showing that $\phi$ is a witness of a simulation of the implementation by the specification}
  
  Because we proved the previous lemma that $\phi$  implied state simulation, the only obligation we have left to prove is showing that $\phi\; i\; s$ is preserved by both action-method transitions and rule transitions, see Figure~\ref{fig:simulation}.

  Let's start with the statement of the theorem:

.. coq:: fold 
|*)

Theorem correct : refines mkRf4 mkRfSpec ϕ. (* .in *)
  (* We start by using the proof tactic [prove_refinement]. This tactic unfolds
  the definition of [refines] and creates one subgoal per action method and per
  rule of the implementation module. The content of those subgoals is to prove that [ϕ]
  is preserved by all transition relations and that state simulation is preserved.  
  As we already showed a lemma that [ϕ] implies state simulation, the second proof
  obligation will be simply a consequence of our lemma. *)
  prove_refinement. (* .in *)
  {(* .in *)
    assert (exists idx newval, {# idx newval} = arg_method) by (
    exists (split1 arg_method);
    exists (split2 arg_method); simpl; merge_simpl; reflexivity);  destruct H as [idx H]; destruct H as [newval H]; subst. (* .none *)
    (* As the implementation module (our 4-register register file),
    does not have any rules and only has one action method, the [write_rf] method,
    there is a single subgoal. *)
    clear indistinguishable_i_s; light_clean_propagate.  (* .none *)
    Opaque RfSpec.write. (* .none *)
    Opaque indistinguishable. (* .none *)
    Opaque mkRfSpec. (* .none *)
    Opaque ϕ. (* .none *)
    move HB at bottom. (* .none *)
    print_arrays. (* .no-in .unfold -.h#* .h#HA1 .h#HB  .h#related_i_s *)
    Transparent ϕ. (* .none *)
    simpl in related_i_s. (* .none *)
    Opaque ϕ. (* .none *)
    (* We have 3 interesting hypotheses: 
    - Hypotheses [HA1] and [HB] state that we can call the [read_rf] value method
    starting in state [st], producing a log [nA], and that applying the update inside
    [nA] to [st] will lead to a state [nxt_st].  
    
    - [related_i_s] is stating that [ϕ] relates the starting implementation
    state to the specification state.
    
    Now we can use our symbolic-evaluation tactic, which will invert the
    hypotheses [HA1] and [related_i_s] to deduce a set of possible cases for these
    assumptions to be true. *)
    symb_ex_split. (* .in *)
    {(* .in *)
      merge_simpl. (* .none *)
      Transparent RfSpec.write. (* .none *)
      Transparent mkRfSpec. (* .none *)
      (* Similarly to the previous proof, using our symbolic-evaluation tactic,
      Coq generated 5 cases (in 5 different subgoals). The first four are
      similar, so let's only detail one of them. 
      
      The reader should notice that the goal here is exactly what was presented
      in Figure 3.1, we are requested to prove that we can call the [write_rf]
      method of the specification starting from our initial specification state.
      This will lead us to a new state [almost_mid_s], and then we have an
      opportunity to execute an arbitrary sequence of rules of the specification
      that should lead us to a state [mid_s] such that [ϕ] relates the end states of
      implementation and specification. *)
      idtac. (* .no-in .unfold -.h#* .h#Heqb .h#Heqb0 .h#Heqb1 .h#Heqb2 .h#HA .h#array_ext .h#array_ext0  .h#array_ext1 .h#array_ext2 *)
      (* In this case, we are not expecting to perform any rule on the
      specification side to catch up with the implementation, so we use our
      tactic [replay_method_with_no_rules], which takes as an argument the lemma
      that proved [phi] indeed implies state simulation. *)
      replay_method_with_no_rules ϕ_implies_state_simul. (* .no-in .unfold -.h#* .h#Heqb .h#Heqb0 .h#Heqb1 .h#Heqb2 .h#HA .h#array_ext .h#array_ext0 .h#array_ext1 .h#array_ext2 *)
      (* Hence we are left with proving that [ϕ] relates the new state of the
      implementation and the new state of the specification.
      We can unfold those definitions and manipulate the expression a bit:*) 
      Transparent ϕ. (* .none *)
      simpl. (* .none *)
      rm_existentials; print_arrays; split; eauto; merge_simpl; simpl. (* .unfold -.h#* .h#Heqb .h#Heqb0 .h#Heqb1 .h#Heqb2 .h#HA .h#array_ext .h#array_ext0  .h#array_ext1 .h#array_ext2 *)
      (* After this simple tactic to unfold and clean up the goal, we are
      requested to provide [?r0] [?r1] [?r2] [?r3] (existential variables), 
      verifying a bunch of simple equations.
      
      Remember that in our case, [idx] is actually a concrete value, so we can
      rewrite our goal by using this assumption and propagate the simplification to the
      constraints. *) 
      rewrite Heqb; simpl; split; eauto.  (* .unfold -.h#* .h#array_ext .h#array_ext0  .h#array_ext1 .h#array_ext2 *) 
      (* We are left with a goal of equality between two symbolic arrays, under
      some assumptions.  To prove this kind of equality between arrays we have
      built a custom tactic: *)
      wrapped_arrays_equal 4%nat. (* .in *)
    }(* .in *)
    Transparent RfSpec.write. (* .none *)
    Transparent mkRfSpec. (* .none *)
    Transparent ϕ . (* .none *)
    all: merge_simpl. (* .none *)
    (* Similarly we handle the 3 other cases corresponding to [idx] = 0,1 and 2,
    which we hide in this literate-programming development. One can check out
    the source code to see them. *) 
    Ltac t idx := replay_method_with_no_rules ϕ_implies_state_simul;
                rm_existentials;
                split; eauto; simpl;
                match goal with
                | [ H: idx = _ |- _] =>
                let t := type of H in
                idtac H t;
                rewrite H
                end;
                simpl;
                split; eauto;
                wrapped_arrays_equal 4%nat . (* .none *)
    1-3: t idx. (* .none *)
    {(* .in *)
      merge_simpl. (* .none *)
      (* We are left with a single goal, as in the previous proof, which is
      contradictory, so we use the same [arithmetic_hammer] tactic.*)
      idtac. (* .no-in .unfold -.h#* .h#Heqb .h#Heqb2 .h#Heqb0 .h#Heqb1 .h#HA *)
      arithmetic_hammer. (* .unfold *)
    } (* .in *)
  }
  Qed.
 


