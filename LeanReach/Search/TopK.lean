namespace LeanReach.TopK

universe u

private def heapifyDown {α : Type u} [Inhabited α] (better : α → α → Bool)
    (items : Array α) : Array α := Id.run do
  let mut items := items
  let mut parent : Nat := 0
  while 2 * parent + 1 < items.size do
    let left := 2 * parent + 1
    let right := left + 1
    let child :=
      if right < items.size && better items[left]! items[right]! then right else left
    if better items[parent]! items[child]! then
      items := items.swapIfInBounds parent child
      parent := child
    else break
  return items

private def heapInsert {α : Type u} [Inhabited α] (better : α → α → Bool)
    (items : Array α) (item : α) : Array α := Id.run do
  let mut items := items.push item
  let mut child := items.size - 1
  while child > 0 do
    let parent := (child - 1) / 2
    if better items[parent]! items[child]! then
      items := items.swapIfInBounds parent child
      child := parent
    else break
  return items

def select {α : Type u} [Inhabited α] (size limit : Nat)
    (item : Nat → α) (better : α → α → Bool) : Array α := Id.run do
  if limit == 0 || size == 0 then return #[]
  let best :=
    if size ≤ limit then
      (Array.range size).map item
    else Id.run do
      let mut heap := #[]
      for position in [0:size] do
        let candidate := item position
        if heap.size < limit then
          heap := heapInsert better heap candidate
        else if better candidate heap[0]! then
          heap := heapifyDown better (heap.set! 0 candidate)
      return heap
  return best.qsort better

end LeanReach.TopK
