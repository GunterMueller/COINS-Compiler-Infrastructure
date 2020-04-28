/* ---------------------------------------------------------------------
%   Copyright (C) 2007 Association for the COINS Compiler Infrastructure
%       (Read COPYING for detailed information.)
--------------------------------------------------------------------- */
package coins.sym;


//========================================//

/** Param interface
 *  Param class (formal parameter class) interface.
 *  Anonymous parameter should be assigned a generated name.
**/
public interface
Param extends Var
{

/** getParamIndex
 *  Get parameter index.
 *  See setNextVar(...), DefinedIn( ).
 *  @return parameter index (1: first parameter, 2: second parameter,
 *      3: third parameter, etc. in DefinedIn( ) subprogram).
**/
int  getParamIndex( );

/** setParamIndex
 *  Set parameter index.
 *  See setNextVar(...), DefinedIn( ).
 *  @param pIndex index value to be set to this parameter.
 *  @return parameter index (1: first parameter, 2: second parameter,
 *      : third parameter, etc. in DefinedIn( ) subprogram).
**/
void setParamIndex( int pIndex );

/** isOptionalParam      (##2)
 *  See if this is optional parameter generated for "..." specification.
 *  See setOptionalParam in Subp.
 *  @return true if this is an optional paramater generated by
 *      setOptionalParam in SubpInterface, false otherwise.
**/
boolean
isOptionalParam( );

/** markAsOptional
 *  Mark this parameter as optional.
**/
public void
markAsOptional();

/** Mark this parameter as call-by-reference **/
public void
markAsCallByReference();

/** Mark this parameter as call-by-value **/
public void
markAsCallByValue();

/** true if this parameter is call-by-reference,
    false otherwise.
**/
public boolean
isCallByReference();

/** true if this parameter is call-by-value,
    false otherwise.
**/
public boolean
isCallByValue();

/** getSubp
 *  @return the subprogram defining this parameter.
**/
public Subp
getSubp();

/** get array parameter size.
    @return  array parameter size
**/
public long 
getArrayParamSize(); //SF030531

/** set array parameter size.
    @param  s  array parameter size
**/
public void
setArrayParamSize(long s); //SF030531  

} // Param interface
