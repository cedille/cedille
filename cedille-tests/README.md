# Instructions for Cedille Tests


## File Structure

| File Structure | Description |
|:-------------- |:----------- |
| cedille/cedille-mode/tests/ | Test directory |
| &nbsp; &nbsp; TESTNAME.cedtest/ | Individual test name |
| &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; script.el | File that is executed during test; should set the value of 'output to a string |
| &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; code.ced | Cedille file to process |
| &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; expected | Expected output, generated when you use the --init option for run-tests.sh |
| &nbsp; &nbsp; &nbsp; &nbsp; &nbsp; actual | Actual output, which is compared to expected |


## Setting Up a Test

To set up a test, you need a Cedille file named code.ced and an elisp file named script.el.

When running a test, script.el will be run **after** code.ced has been checked and the parse tree assembled. The code in script.el should set the value of `'output` to be a string, which will then written to ./actual (or ./expected, with \-i / \-\-init).

The elisp function `cedille-test-perform-key-events (&rest keystrokes)` executes `keystrokes` as if they were typed by the user.

To initialize the expected output of a test:
`./run-tests.sh -i -f TEST.cedtest`

To initialize the expected outputs of all tests:
`./run-tests.sh -i`
