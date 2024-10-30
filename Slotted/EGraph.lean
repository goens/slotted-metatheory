set_option autoImplicit false
abbrev Fun := String
abbrev EClassId := Nat
abbrev Slot := Nat
abbrev SlotMap := List (Slot × Slot)

inductive Term
  | const : Fun → Term
  | eapp : Fun → List Term → Term
  | slot : Slot → Term
  | lam : Slot → Term → Term

inductive ENode
  | const : Fun → ENode
  | eapp : Fun → List EClassId → ENode
  | slot : Slot → ENode
  | lam : Slot → ENode → ENode

abbrev EClass := List ENode

def ENode.eClassIds : ENode → List EClassId
  | ENode.const _ => []
  | ENode.eapp _ ids => ids
  | ENode.slot _ => []
  | ENode.lam _ nd => nd.eClassIds

def EClass.eClassIds : EClass → List EClassId :=
  List.join ∘ List.map ENode.eClassIds

structure EGraph where
  -- data
  classes : List EClass
  map? : EClassId → Option EClass

def EGraph.eClassIds (E : EGraph) : List EClassId :=
  E.classes.map EClass.eClassIds |>.join

def EGraph.eNodes (E : EGraph) (a : EClassId) : List ENode :=
  match E.map? a with
    | some ec => ec
    | none => []

structure EGraph.WellFormed (E : EGraph) where
  map_classes : ∀ (ec : EClass)(a : EClassId), E.map? a = some ec → ec ∈ E.classes
  map_total : ∀ a ∈ E.eClassIds, E.map? a |>.isSome

def EGraph.map {E : EGraph} (hwf : E.WellFormed) (a : EClassId) (ha : a ∈ E.eClassIds := by decide) : EClass :=
  match hmap : E.map? a with
    | some ec => ec
    | none => False.elim (let_fun hcontra := hwf.map_total a ha;
    Bool.noConfusion (Eq.mp (congrArg (fun _a => _a.isSome = true) hmap) hcontra))

def Term.isUnslotted : Term → Prop
  | Term.const _ => True
  | Term.eapp _ args => ∀ arg ∈ args, arg.isUnslotted
  | Term.slot _ => False
  | Term.lam _ _ => False

def EGraph.node_mem  (E : EGraph) (nd : ENode) : Prop :=
  ∃ ec ∈ E.classes, nd ∈ ec

def EGraph.id_mem  (E : EGraph) (id : EClassId) : Prop :=
  E.map? id |>.isSome

instance : Membership ENode EGraph := ⟨EGraph.node_mem⟩
instance : Membership EClassId EGraph := ⟨EGraph.id_mem⟩

-- Note: unclear if it's easier to just define a separate inductive and define the injection
inductive ENode.isUnslotted {E : EGraph} : ENode → Prop
  | const : ENode.isUnslotted (ENode.const _)
  | eapp : ∀ f args, (∀ arg ∈ args, ∀ cl, E.map? arg = some cl → ∀ nd ∈ cl, nd.isUnslotted) → ENode.isUnslotted (ENode.eapp f args)

def EGraph.decideUnlsotted {E : EGraph} {hwf : E.WellFormed} {nd : ENode} : Decidable (ENode.isUnslotted (E:=E) nd) :=
  match nd with
   | ENode.const _ => isTrue ENode.isUnslotted.const
   | ENode.slot _ => isFalse (by intro hcontra; cases hcontra)
   | ENode.lam _ _ => isFalse (by intro hcontra; cases hcontra)
   | ENode.eapp f [] => isTrue (ENode.isUnslotted.eapp f [] (by intro a h; cases h))
   | ENode.eapp f (arg::args) => match EGraph.decideUnlsotted (E:=E) (hwf:=hwf) (nd:=ENode.eapp f args) with
     | isFalse h => isFalse (by sorry)
     | isTrue h => match harg : E.map? arg with
       | some cl => sorry
       | none => isTrue (ENode.isUnslotted.eapp f (arg::args) (by sorry))

instance {E : EGraph} {nd : ENode} {hwf : E.WellFormed} : Decidable (nd.isUnslotted (E:=E)) :=
  @EGraph.decideUnlsotted E hwf nd
