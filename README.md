# dataOfGADT
generate Data.Data instance for GADT

## project is dead

+ the basic was to group the GADT constructors by its result type. and create data-derivable wrapper newtype for each of them. 
+ however, this approach leads to dead end because doesnot apply to a recursive GADT.
