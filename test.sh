#!/bin/bash
# Requires bash version >= 4 and GNU grep
# minizinc and fzn-gecode should be added to PATH 
# Result: test.log file, where every line says if the test has been passed

GREP="grep"
is_grep_gnu=$(grep --version | grep "GNU grep")
if [ -z "$is_grep_gnu" ]; then 
    # on macos ggrep is a popular alias for gnu grep
    GREP="ggrep"
fi

declare -A test_cases=( 
    ["data/fgc_01_01_01_00.dzn"]="15"
    ["data/fgc_05_01_01_00.dzn"]="61" 
    ["data/fgc_05_05_05_00.dzn"]="50" 
    ["data/fgc_06_07_20_00.dzn"]="224" 
    )

dir=$(cd -P -- "$(dirname -- "$0")" && pwd -P)

model_basename="foxgeesecorn" 
model="$model_basename.mzn"
output_fzn="$model_basename.fzn"
output_ozn="$model_basename.ozn"
compile_test="data/fgc_06_26_08_00.dzn"
timelimit=2000

syntax_errors=$(minizinc --instance-check-only $model $compile_test 2>&1)
test_result="FAIL"
if [ -z "$syntax_errors" ]; then
    test_result="PASS"
fi
echo "building: $test_result"

for data in "${!test_cases[@]}"; do
    [ -e "$data" ] || continue
    expected=${test_cases["$data"]}
    full_result=$(minizinc -c --ozn $output_ozn --solver Gecode $model  2>&1 $data && fzn-gecode -time $timelimit $output_fzn | minizinc --ozn-file $output_ozn)
    
    error=$(echo "$full_result" | $GREP "Error:")
    if [ -n "$error" ]; then 
        echo -e "$data: FAIL (bulding error)"
        continue
    fi
    
    timeout=$(echo "$full_result" | $GREP "=====UNKNOWN=====")
    if [ -n "$timeout" ]; then 
        echo -e "$data: FAIL (timeout - no solution at all)"
        continue
    fi

    timeout=$(echo "$full_result" | $GREP "==========")
    if [ -z "$timeout" ]; then 
        echo -e "$data: FAIL (timeout - no optimal solution)"
        continue
    fi

    result=$(echo "$full_result" | $GREP -P 'obj\s*=\s*\d+;' | cut -d"=" -f2 | awk '{print substr($1, 1, length($1)-1)}')

    if [ -z "$result" ]; then 
        test_result="FAIL (output is missing 'obj = <result>;' line)"
    elif [ "$expected" == "$result" ]; then
        test_result="PASS"
    else
        test_result="FAIL (expected optimum solution should have obj = $expected, got $result)"
    fi

    echo -e "$data: $test_result"
done

rm $output_fzn 2>/dev/null || true 
rm $output_ozn 2>/dev/null || true
