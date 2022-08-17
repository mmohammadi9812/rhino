module Test where
import Prelude


main :: IO Int
main = do
    let y = primIntAdd 0 2 * 4
    putStrLn "test"
    return y


