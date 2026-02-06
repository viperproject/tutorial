# Viper's Program State

Permissions are a part of a Viper program's state, alongside the values of variables and heap locations. Fields are only the first of several kinds of *resource* that will be explained in this tutorial; access to each resource is governed by appropriate permissions.
Different permissions can be held at different points in a Viper program: e.g., after allocating new memory on the heap, we would typically also add the permission to access those locations. In the next subsection, we will see the primitive operations Viper provides for manipulating the permissions currently held.

A program state in Viper consists of:

* The values of all variables in scope: these include local variables, method input parameters (which cannot be assigned to in Viper), and method return parameters (which can) of the current method execution. Verification in Viper is *method-modular*: each method implementation is verified in isolation and, thus, the program state does not contain an explicit call stack.
* The permissions to field locations held by the current method execution.
* The values of those field locations to which permissions are currently held. Other field locations cannot be accessed.

The initial state of each method execution contains arbitrary values (of the appropriate types) for all variables in scope, and no permissions to heap locations. Permissions can be obtained through a suitable precondition (as in the `inc` example above); preconditions can also constrain the values of parameters and heap locations. Field locations to which permission is newly obtained will also contain arbitrary values.
