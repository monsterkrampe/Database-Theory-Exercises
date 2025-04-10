-- Many basic definitions are taken from (or at least inspired by) https://lean-lang.org/functional_programming_in_lean/dependent-types/typed-queries.html

inductive DBType where
| int | string | bool
deriving DecidableEq

abbrev DBType.asType : DBType → Type
| .int => Int
| .string => String
| .bool => Bool

def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y

instance {t : DBType} : BEq t.asType where
  beq := t.beq

structure SchemaCol where
  name : String
  dbType : DBType
deriving DecidableEq

abbrev TableSchema := List SchemaCol

abbrev Row : TableSchema -> Type
| [] => Unit
| [col] => col.dbType.asType
| col1 :: col2 :: cols => col1.dbType.asType × Row (col2::cols)

def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'

instance : BEq (Row s) where
  beq := Row.bEq

abbrev Table (s : TableSchema) := List (Row s)

def Table.distinct (t : Table s) : Table s := t.eraseDups

inductive HasCol : TableSchema → String → DBType → Type where
| here : HasCol (⟨name, t⟩ :: _) name t
| there : HasCol s name t → HasCol (_ :: s) name t

def TableSchema.has_col (s : TableSchema) (col : SchemaCol) : Option (HasCol s col.name col.dbType) :=
  match s with
  | [] => none
  | c :: s =>
    if h : c = col
    then .some (cast (by rw [h]) (@HasCol.here s c.name c.dbType))
    else
      let res := TableSchema.has_col s col
      res.map (fun hasCol => .there hasCol)

theorem TableSchema.has_col_isSome_of_mem (s : TableSchema) (col : SchemaCol) : col ∈ s -> (s.has_col col).isSome := by
  induction s with
  | nil => simp
  | cons hd tl ih =>
    rw [List.mem_cons]
    intro h
    simp only [has_col]
    cases Decidable.em (hd = col) with
    | inl eq => simp [eq]
    | inr neq =>
      simp only [neq, Bool.false_eq_true, ↓reduceDIte, Option.isSome_map']
      apply ih
      cases h with
      | inl h => rw [h] at neq; simp at neq
      | inr h => exact h

def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next

inductive Subschema : TableSchema → TableSchema → Type where
  | nil : Subschema [] bigger
  | cons :
      HasCol bigger n t →
      Subschema smaller bigger →
      Subschema (⟨n, t⟩ :: smaller) bigger

def Subschema.addColumn (sub : Subschema smaller bigger) : Subschema smaller (c :: bigger) :=
  match sub with
  | .nil  => .nil
  | .cons col sub' => .cons (.there col) sub'.addColumn

def Subschema.reflexive : (s : TableSchema) → Subschema s s
  | [] => .nil
  | _ :: cs => .cons .here (reflexive cs).addColumn

def Row.project (row : Row s) : (s' : TableSchema) → Subschema s' s → Row s'
  | [], .nil => ()
  | [_], .cons c .nil => row.get c
  | _::_::_, .cons c cs => (row.get c, row.project _ cs)

def Table.project (table : Table s) (s' : TableSchema) (sub : Subschema s' s) : Table s' := table.map (fun row => row.project s' sub)

inductive SelectionArgument (left : HasCol s n t) where
| const : t.asType -> SelectionArgument left
| col : HasCol s n2 t -> SelectionArgument left

def Row.select (row : Row s) (left : HasCol s n t) (arg : SelectionArgument left) : Bool :=
  match arg with
  | .const c => row.get left == c
  | .col right => row.get left == row.get right

def Table.select (table : Table s) (left : HasCol s n t) (arg : SelectionArgument left) : Table s := table.filter (fun row => row.select left arg)

def TableSchema.renameColumn : (s : TableSchema) → HasCol s n t → String → TableSchema
| c :: cs, .here, n' => {c with name := n'} :: cs
| c :: cs, .there next, n' => c :: renameColumn cs next n'

def Row.addVal (v : c.dbType.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | _ :: _, v' => (v, v')

def Row.rename (row : Row s) (col : HasCol s n t) (newName : String) : Row (s.renameColumn col newName) :=
  match s, row, col with
  | [_], v, .here => v
  | _::_::_, (v, r), .here => addVal v r
  | _::_::_, (v, r), .there next => addVal v (r.rename next newName)

def Table.rename (t : Table s) (col : HasCol s n ty) (newName : String) : Table (s.renameColumn col newName) :=
  t.map (fun r => r.rename col newName)

def Table.diff (t1 t2 : Table s) : Table s := t1.filter (fun r => !t2.contains r)

def Table.union (t1 t2 : Table s) : Table s := t1 ++ t2

def Table.intersection (t1 t2 : Table s) : Table s := t1.filter (fun r => t2.contains r)


-- Natural Join starts here - couple of ingredients needed

def TableSchema.dropColumns (s : TableSchema) (cols : TableSchema) : TableSchema := s.filter (fun c => ¬ c ∈ cols)

def Subschema.dropColumns (s: TableSchema) (cols : TableSchema) : Subschema (s.dropColumns cols) s :=
  match s with
  | [] => .nil
  | hd::tl =>
    let sub : Subschema (TableSchema.dropColumns tl cols) (hd::tl) := Subschema.addColumn (Subschema.dropColumns tl cols)
    if h : hd ∈ cols
    then
      cast (by
        unfold TableSchema.dropColumns
        rw [List.filter_cons]
        simp [h]
      ) sub
    else
      cast (by
        unfold TableSchema.dropColumns
        rw [List.filter_cons]
        simp [h]
      ) (Subschema.cons HasCol.here sub)

def Row.dropColumns (row : Row s) (cols : TableSchema) : Row (s.dropColumns cols) :=
  row.project _ (Subschema.dropColumns s cols)

def Row.concat (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal v r2
  | _::_::_, (v, r1) => addVal v (concat r1 r2)

def Row.colsMatch (r1 : Row s1) (r2 : Row s2) (left : HasCol s1 n t) (right : HasCol s2 n t) : Bool :=
  r1.get left == r2.get right

def Row.matchesOnCol (r1 : Row s1) (r2 : Row s2) (col : SchemaCol) : Bool :=
  match s1.has_col col with
  | .none => false
  | .some left => match s2.has_col col with
    | .none => false
    | .some right => colsMatch r1 r2 left right

def Row.joinOn (r1 : Row s1) (r2 : Row s2) (joinCols : TableSchema) : Option (Row (s1 ++ s2.dropColumns joinCols)) :=
  if joinCols.all (fun col => Row.matchesOnCol r1 r2 col)
  then .some (r1.concat (r2.dropColumns joinCols))
  else .none

def Row.naturalJoin (r1 : Row s1) (r2 : Row s2) : Option (Row (s1 ++ s2.dropColumns (s1.filter (fun c => c ∈ s2)))) :=
  let joinCols := s1.filter (fun c => c ∈ s2)
  Row.joinOn r1 r2 joinCols

def Table.naturalJoin (t1 : Table s1) (t2 : Table s2) : Table (s1 ++ s2.dropColumns (s1.filter (fun c => c ∈ s2))) :=
  t1.flatMap (fun r1 =>
    t2.filterMap (fun r2 =>
      r1.naturalJoin r2
    )
  )

