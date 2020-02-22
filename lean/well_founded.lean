universe u

variable α : Sort u

variable r : α → α → Prop

#check (acc r)          -- α → Prop

#check (well_founded r) -- Prop

-- acc r x expresses that 'x is accessible from below', i.e. all
-- its predecessors are accessible from below
lemma L1 : ∀ (x:α), acc r x ↔ ∀ (y:α), r y x → acc r y := _
