import Data.TPTP
import Data.TPTP.Parse.Text
import Data.TPTP.Pretty
import Data.Text

test :: Text
test =
    pack
        "cnf(member_of_union_is_member_of_one_set,axiom,\
        \( ~ union(Set1,Set2,Union)\
        \| ~ member(Element,Union)\
        \| member(Element,Set1)\
        \| member(Element,Set2) ) )."

out :: TPTP
out = case parseTPTPOnly test of
    Left _ -> error "oops"
    Right out -> out
