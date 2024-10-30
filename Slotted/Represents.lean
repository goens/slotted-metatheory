--import Batteries.Data.List.Basic
import Slotted.EGraph
set_option autoImplicit false
--open Batteries

mutual
def ENode.Represents (E : EGraph) : ENode → Term → Prop
  | ENode.const f, Term.const f' => f = f'
  | ENode.slot s, Term.slot s' => s = s'
  | ENode.lam s nd, Term.lam s' nd' => s = s' ∧ ENode.Represents E nd nd'
  -- This version is nicer but the termination checker can't see through the List.Forall₂
  --| ENode.eapp f args, Term.eapp f' args' => f = f' ∧ List.Forall₂ (EClassId.Represents E) args args'
  | ENode.eapp f [], Term.eapp f' [] => f = f'
  | ENode.eapp f (arg::args), Term.eapp f' (arg'::args') => EClassId.Represents E arg arg' ∧ ENode.Represents E (ENode.eapp f args) (Term.eapp f' args')
  | _, _ => False

def EClassId.Represents (E : EGraph) : EClassId → Term → Prop
  | id, t => ∃ nd ∈ E.eNodes id, (ENode.Represents E) nd t
end

def EClass.Represents (E : EGraph) : EClass → Term → Prop
  | cl, tm => ∃ nd ∈ cl, ENode.Represents E nd tm

def EGraph.Represents (E : EGraph) : Term → Prop
  | t => ∃ cl ∈ E.classes, EClass.Represents E cl t
