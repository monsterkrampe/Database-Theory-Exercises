import DatabaseTheory.RelationalAlgebra

def S_Films : TableSchema := [
  { name := "Title", dbType := DBType.string },
  { name := "Director", dbType := DBType.string },
  { name := "Actor", dbType := DBType.string },
]

def S_Venues : TableSchema := [
  { name := "Cinema", dbType := DBType.string },
  { name := "Address", dbType := DBType.string },
  { name := "Phone", dbType := DBType.string },
]

def S_Program : TableSchema := [
  { name := "Cinema", dbType := DBType.string },
  { name := "Title", dbType := DBType.string },
  { name := "Time", dbType := DBType.string },
]

def T_Films : Table S_Films := [
  ("The Imitation Game", "Tyldum", "Cumberbatch"),
  ("The Imitation Game", "Tyldum", "Knightley"),
  ("The Internet's Own Boy", "Knappenberger", "Swartz"),
  ("The Internet's Own Boy", "Knappenberger", "Lessig"),
  ("The Internet's Own Boy", "Knappenberger", "Berners-Lee"),
  ("Dogma", "Smith", "Damon"),
  ("Dogma", "Smith", "Affleck"),
  ("Dogma", "Smith", "Morissette"),
  ("Dogma", "Smith", "Smith"),
  ("Film by Smith I made up", "Smith", "Damon"),
  ("Film by Smith I made up", "Smith", "Morissette"),
  ("Film not by Smith I made up", "Not Smith", "Damon"),
  ("Film by Knappenberger I made up", "Knappenberger", "Cumberbatch"),
  ("Film by Knappenberger I made up", "Knappenberger", "Knightley"),
  ("Film by Knappenberger I made up", "Knappenberger", "Damon"),
  ("Film by Knappenberger I made up", "Knappenberger", "Affleck"),
  ("Film by Knappenberger I made up", "Knappenberger", "Morissette"),
  ("Film by Knappenberger I made up", "Knappenberger", "Smith"),
]

def T_Venues : Table S_Venues := [
  ("UFA", "St. Petersburger Str. 24", "4825825"),
  ("Schauburg", "St. Petersburger Str. 24", "8032185"),
  ("CinemaxX", "Hüblerstr. 8", "3158910"),
]

def T_Program : Table S_Program := [
  ("Schauburg", "The Imitation Game", "19:30"),
  ("Schauburg", "Dogma", "20:45"),
  ("Ufa", "The Imitation Game", "22:45"),
  ("CinemaxX", "The Imitation Game", "19:30"),
]

-- Exercise 1.1

-- 1. Director of Imitation Game
#eval (T_Films.select .here (.const "The Imitation Game")).project _ (.cons (.there .here) .nil)

-- 2. Cinemas with Imitation Game
-- Note: instead of using here/there we obtain HasCol from the name of the column but this is also quite verbose
#eval (T_Program.select ((S_Program.has_col { name := "Title", dbType := DBType.string }).get (by apply TableSchema.has_col_isSome_of_mem; decide)) (.const "The Imitation Game")).project _ (.cons .here .nil)

-- 3. Address and Phone of Schauburg
#eval (T_Venues.select .here (.const "Schauburg")).project _ (.cons (.there .here) (.cons (.there (.there .here)) .nil))

-- 4. Film by Smith playing? (Empty List indicates false, List with any positive number of () indicates true)
#eval ((T_Films.select (.there .here) (.const "Smith")).naturalJoin T_Program).project _ .nil

-- 5. Director directed Actor and vice versa
#eval ((((((T_Films.rename .here "T").rename (.there .here) "D").rename (.there (.there .here)) "A").naturalJoin T_Films).select (.there .here) (.col (.there (.there (.there (.there (.there .here))))))).select (.there (.there .here)) (.col (.there (.there (.there (.there .here)))))).project _ (.cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil))

-- 6. Directors acting in their film
#eval (T_Films.select (.there .here) (.col (.there (.there .here)))).project _ (.cons (.there .here) .nil)

-- 7. Fixed table (we allow constant tables with single columns here only)
def T_Constant_Title : Table [{name := "Title", dbType := DBType.string}] := [("Apocalypse Now")]
def T_Constant_Director : Table [{name := "Director", dbType := DBType.string}] := [("Coppola")]
#eval T_Constant_Title.naturalJoin T_Constant_Director

-- 8. Actors in Film by Smith
#eval (T_Films.select (.there .here) (.const "Smith")).project _ (.cons (.there (.there .here)) .nil)

-- 9. Actors in every film by smith
-- aux: actors not in some film by smith
def aux_table_for_9 := (((T_Films.project _ (.cons (.there (.there .here)) .nil)).naturalJoin ((T_Films.select (.there .here) (.const "Smith")).project _ (.cons .here .nil))).diff ((T_Films.select (.there .here) (.const "Smith")).project _ (.cons (.there (.there .here)) (.cons .here .nil)))).project _ (.cons .here .nil)
#eval aux_table_for_9
#eval (T_Films.project _ (.cons (.there (.there .here)) .nil)).diff aux_table_for_9

-- 10. actors only in films by smith
#eval (T_Films.project _ (.cons (.there (.there .here)) .nil)).diff ((T_Films.diff (T_Films.select (.there .here) (.const "Smith"))).project _ (.cons (.there (.there .here)) .nil))

-- 11. actors acting together in at least one film
#eval ((T_Films.rename (.there (.there .here)) "RA").naturalJoin T_Films).project _ (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil))

-- 12. actors cast in exactly the same films
def aux_table_for_12_1_1 := ((T_Films.project _ (.cons (.there (.there .here)) .nil)).naturalJoin (T_Films.rename (.there (.there .here)) "RA")).project _ (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there .here))) .nil))))
def aux_table_for_12_1_2 := T_Films.naturalJoin ((T_Films.project _ (.cons (.there (.there .here)) .nil)).rename .here "RA")
def aux_table_for_12_1 := (aux_table_for_12_1_1.diff aux_table_for_12_1_2).project _ (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))
/- #eval aux_table_for_12_1_1 -/
/- #eval aux_table_for_12_1_2 -/
#eval aux_table_for_12_1
def aux_table_for_12_2 := ((T_Films.project _ (.cons (.there (.there .here)) .nil)).naturalJoin ((T_Films.project _ (.cons (.there (.there .here)) .nil)).rename .here "RA")).diff aux_table_for_12_1
#eval aux_table_for_12_2
#eval (aux_table_for_12_2.naturalJoin (((aux_table_for_12_2.rename .here "TMP").rename (.there .here) "Actor").rename .here "RA")).distinct

-- 13. directors directing every actor
#eval ((T_Films.project _ (.cons (.there .here) .nil)).diff ((((T_Films.project _ (.cons (.there .here) .nil)).naturalJoin (T_Films.project _ (.cons (.there (.there .here)) .nil))).diff (T_Films.project _ (.cons (.there .here) (.cons (.there (.there .here)) .nil)))).project _ (.cons .here .nil))).distinct

