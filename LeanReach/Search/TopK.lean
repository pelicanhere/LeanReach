namespace LeanReach.TopK

universe u

private def heapifyDown {α : Type u} [Inhabited α] (better : α → α → Bool)
    (items : Array α) : Array α :=
  let rec go (steps : Nat) (items : Array α) (parent : Nat) : Array α :=
    match steps with
    | 0 => items
    | steps + 1 =>
      if 2 * parent + 1 < items.size then
        let left := 2 * parent + 1
        let right := left + 1
        let child :=
          if right < items.size && better items[left]! items[right]! then right else left
        if better items[parent]! items[child]! then
          go steps (items.swapIfInBounds parent child) child
        else items
      else items
  go items.size items 0

private def heapInsert {α : Type u} [Inhabited α] (better : α → α → Bool)
    (items : Array α) (item : α) : Array α :=
  let result := items.push item
  let rec go (steps : Nat) (result : Array α) (child : Nat) : Array α :=
    match steps with
    | 0 => result
    | steps + 1 =>
      if child > 0 then
        let parent := (child - 1) / 2
        if better result[parent]! result[child]! then
          go steps (result.swapIfInBounds parent child) parent
        else result
      else result
  go result.size result (result.size - 1)

def select {α : Type u} [Inhabited α] (size limit : Nat)
    (item : Nat → α) (better : α → α → Bool) : Array α :=
  if limit == 0 || size == 0 then #[]
  else
    let best :=
      if size ≤ limit then
        (Array.range size).map item
      else
        (Array.range size).foldl (init := (#[] : Array α)) fun heap position =>
          let candidate := item position
          if heap.size < limit then
            heapInsert better heap candidate
          else if better candidate heap[0]! then
            heapifyDown better (heap.set! 0 candidate)
          else heap
    best.qsort better

end LeanReach.TopK
