data Option (A : Set) : Set where
  empty : Option A
  item  : A → Option A
