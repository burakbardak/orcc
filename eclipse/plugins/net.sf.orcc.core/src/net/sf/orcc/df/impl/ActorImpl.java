/**
 * <copyright>
 * </copyright>
 *
 * $Id$
 */
package net.sf.orcc.df.impl;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import net.sf.orcc.df.Action;
import net.sf.orcc.df.Actor;
import net.sf.orcc.df.DfPackage;
import net.sf.orcc.df.FSM;
import net.sf.orcc.df.Port;
import net.sf.orcc.ir.Procedure;
import net.sf.orcc.ir.Var;
import net.sf.orcc.ir.util.MapAdapter;
import net.sf.orcc.moc.MoC;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.NotificationChain;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.InternalEObject;
import org.eclipse.emf.ecore.impl.ENotificationImpl;
import org.eclipse.emf.ecore.util.EObjectContainmentEList;
import org.eclipse.emf.ecore.util.EObjectResolvingEList;
import org.eclipse.emf.ecore.util.InternalEList;

/**
 * <!-- begin-user-doc --> An implementation of the model object '
 * <em><b>Actor</b></em>'. <!-- end-user-doc -->
 * <p>
 * The following features are implemented:
 * <ul>
 *   <li>{@link net.sf.orcc.df.impl.ActorImpl#getActions <em>Actions</em>}</li>
 *   <li>{@link net.sf.orcc.df.impl.ActorImpl#getActionsOutsideFsm <em>Actions Outside Fsm</em>}</li>
 *   <li>{@link net.sf.orcc.df.impl.ActorImpl#getFsm <em>Fsm</em>}</li>
 *   <li>{@link net.sf.orcc.df.impl.ActorImpl#getInitializes <em>Initializes</em>}</li>
 *   <li>{@link net.sf.orcc.df.impl.ActorImpl#getInputs <em>Inputs</em>}</li>
 *   <li>{@link net.sf.orcc.df.impl.ActorImpl#getMoC <em>Mo C</em>}</li>
 *   <li>{@link net.sf.orcc.df.impl.ActorImpl#getOutputs <em>Outputs</em>}</li>
 *   <li>{@link net.sf.orcc.df.impl.ActorImpl#getParameters <em>Parameters</em>}</li>
 *   <li>{@link net.sf.orcc.df.impl.ActorImpl#getProcs <em>Procs</em>}</li>
 *   <li>{@link net.sf.orcc.df.impl.ActorImpl#getStateVars <em>State Vars</em>}</li>
 *   <li>{@link net.sf.orcc.df.impl.ActorImpl#isNative <em>Native</em>}</li>
 * </ul>
 * </p>
 *
 * @generated
 */
public class ActorImpl extends EntityImpl implements Actor {
	/**
	 * The cached value of the '{@link #getActions() <em>Actions</em>}' containment reference list.
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @see #getActions()
	 * @generated
	 * @ordered
	 */
	protected EList<Action> actions;

	/**
	 * The cached value of the '{@link #getActionsOutsideFsm() <em>Actions Outside Fsm</em>}' reference list.
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @see #getActionsOutsideFsm()
	 * @generated
	 * @ordered
	 */
	protected EList<Action> actionsOutsideFsm;

	/**
	 * The cached value of the '{@link #getFsm() <em>Fsm</em>}' containment reference.
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @see #getFsm()
	 * @generated
	 * @ordered
	 */
	protected FSM fsm;

	/**
	 * The cached value of the '{@link #getInitializes() <em>Initializes</em>}' containment reference list.
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @see #getInitializes()
	 * @generated
	 * @ordered
	 */
	protected EList<Action> initializes;

	/**
	 * The cached value of the '{@link #getInputs() <em>Inputs</em>}' containment reference list.
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @see #getInputs()
	 * @generated
	 * @ordered
	 */
	protected EList<Port> inputs;

	private Map<String, Procedure> mapProcedures;

	private Map<String, Var> mapStateVars;

	/**
	 * The cached value of the '{@link #getMoC() <em>Mo C</em>}' containment reference.
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @see #getMoC()
	 * @generated
	 * @ordered
	 */
	protected MoC moC;

	/**
	 * The cached value of the '{@link #getOutputs() <em>Outputs</em>}' containment reference list.
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @see #getOutputs()
	 * @generated
	 * @ordered
	 */
	protected EList<Port> outputs;

	/**
	 * The cached value of the '{@link #getParameters() <em>Parameters</em>}' containment reference list.
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @see #getParameters()
	 * @generated
	 * @ordered
	 */
	protected EList<Var> parameters;

	/**
	 * The cached value of the '{@link #getProcs() <em>Procs</em>}' containment reference list.
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @see #getProcs()
	 * @generated
	 * @ordered
	 */
	protected EList<Procedure> procs;

	/**
	 * The cached value of the '{@link #getStateVars() <em>State Vars</em>}' containment reference list.
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @see #getStateVars()
	 * @generated
	 * @ordered
	 */
	protected EList<Var> stateVars;

	/**
	 * The default value of the '{@link #isNative() <em>Native</em>}' attribute.
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @see #isNative()
	 * @generated
	 * @ordered
	 */
	protected static final boolean NATIVE_EDEFAULT = false;

	/**
	 * The cached value of the '{@link #isNative() <em>Native</em>}' attribute.
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @see #isNative()
	 * @generated
	 * @ordered
	 */
	protected boolean native_ = NATIVE_EDEFAULT;

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 */
	protected ActorImpl() {
		super();

		mapProcedures = new HashMap<String, Procedure>();
		mapStateVars = new HashMap<String, Var>();

		eAdapters().add(new MapAdapter());
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetFsm(FSM newFsm, NotificationChain msgs) {
		FSM oldFsm = fsm;
		fsm = newFsm;
		if (eNotificationRequired()) {
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DfPackage.ACTOR__FSM, oldFsm, newFsm);
			if (msgs == null) msgs = notification; else msgs.add(notification);
		}
		return msgs;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public NotificationChain basicSetMoC(MoC newMoC, NotificationChain msgs) {
		MoC oldMoC = moC;
		moC = newMoC;
		if (eNotificationRequired()) {
			ENotificationImpl notification = new ENotificationImpl(this, Notification.SET, DfPackage.ACTOR__MO_C, oldMoC, newMoC);
			if (msgs == null) msgs = notification; else msgs.add(notification);
		}
		return msgs;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public Object eGet(int featureID, boolean resolve, boolean coreType) {
		switch (featureID) {
			case DfPackage.ACTOR__ACTIONS:
				return getActions();
			case DfPackage.ACTOR__ACTIONS_OUTSIDE_FSM:
				return getActionsOutsideFsm();
			case DfPackage.ACTOR__FSM:
				return getFsm();
			case DfPackage.ACTOR__INITIALIZES:
				return getInitializes();
			case DfPackage.ACTOR__INPUTS:
				return getInputs();
			case DfPackage.ACTOR__MO_C:
				return getMoC();
			case DfPackage.ACTOR__OUTPUTS:
				return getOutputs();
			case DfPackage.ACTOR__PARAMETERS:
				return getParameters();
			case DfPackage.ACTOR__PROCS:
				return getProcs();
			case DfPackage.ACTOR__STATE_VARS:
				return getStateVars();
			case DfPackage.ACTOR__NATIVE:
				return isNative();
		}
		return super.eGet(featureID, resolve, coreType);
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public NotificationChain eInverseRemove(InternalEObject otherEnd,
			int featureID, NotificationChain msgs) {
		switch (featureID) {
			case DfPackage.ACTOR__ACTIONS:
				return ((InternalEList<?>)getActions()).basicRemove(otherEnd, msgs);
			case DfPackage.ACTOR__FSM:
				return basicSetFsm(null, msgs);
			case DfPackage.ACTOR__INITIALIZES:
				return ((InternalEList<?>)getInitializes()).basicRemove(otherEnd, msgs);
			case DfPackage.ACTOR__INPUTS:
				return ((InternalEList<?>)getInputs()).basicRemove(otherEnd, msgs);
			case DfPackage.ACTOR__MO_C:
				return basicSetMoC(null, msgs);
			case DfPackage.ACTOR__OUTPUTS:
				return ((InternalEList<?>)getOutputs()).basicRemove(otherEnd, msgs);
			case DfPackage.ACTOR__PARAMETERS:
				return ((InternalEList<?>)getParameters()).basicRemove(otherEnd, msgs);
			case DfPackage.ACTOR__PROCS:
				return ((InternalEList<?>)getProcs()).basicRemove(otherEnd, msgs);
			case DfPackage.ACTOR__STATE_VARS:
				return ((InternalEList<?>)getStateVars()).basicRemove(otherEnd, msgs);
		}
		return super.eInverseRemove(otherEnd, featureID, msgs);
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public boolean eIsSet(int featureID) {
		switch (featureID) {
			case DfPackage.ACTOR__ACTIONS:
				return actions != null && !actions.isEmpty();
			case DfPackage.ACTOR__ACTIONS_OUTSIDE_FSM:
				return actionsOutsideFsm != null && !actionsOutsideFsm.isEmpty();
			case DfPackage.ACTOR__FSM:
				return fsm != null;
			case DfPackage.ACTOR__INITIALIZES:
				return initializes != null && !initializes.isEmpty();
			case DfPackage.ACTOR__INPUTS:
				return inputs != null && !inputs.isEmpty();
			case DfPackage.ACTOR__MO_C:
				return moC != null;
			case DfPackage.ACTOR__OUTPUTS:
				return outputs != null && !outputs.isEmpty();
			case DfPackage.ACTOR__PARAMETERS:
				return parameters != null && !parameters.isEmpty();
			case DfPackage.ACTOR__PROCS:
				return procs != null && !procs.isEmpty();
			case DfPackage.ACTOR__STATE_VARS:
				return stateVars != null && !stateVars.isEmpty();
			case DfPackage.ACTOR__NATIVE:
				return native_ != NATIVE_EDEFAULT;
		}
		return super.eIsSet(featureID);
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	@SuppressWarnings("unchecked")
	@Override
	public void eSet(int featureID, Object newValue) {
		switch (featureID) {
			case DfPackage.ACTOR__ACTIONS:
				getActions().clear();
				getActions().addAll((Collection<? extends Action>)newValue);
				return;
			case DfPackage.ACTOR__ACTIONS_OUTSIDE_FSM:
				getActionsOutsideFsm().clear();
				getActionsOutsideFsm().addAll((Collection<? extends Action>)newValue);
				return;
			case DfPackage.ACTOR__FSM:
				setFsm((FSM)newValue);
				return;
			case DfPackage.ACTOR__INITIALIZES:
				getInitializes().clear();
				getInitializes().addAll((Collection<? extends Action>)newValue);
				return;
			case DfPackage.ACTOR__INPUTS:
				getInputs().clear();
				getInputs().addAll((Collection<? extends Port>)newValue);
				return;
			case DfPackage.ACTOR__MO_C:
				setMoC((MoC)newValue);
				return;
			case DfPackage.ACTOR__OUTPUTS:
				getOutputs().clear();
				getOutputs().addAll((Collection<? extends Port>)newValue);
				return;
			case DfPackage.ACTOR__PARAMETERS:
				getParameters().clear();
				getParameters().addAll((Collection<? extends Var>)newValue);
				return;
			case DfPackage.ACTOR__PROCS:
				getProcs().clear();
				getProcs().addAll((Collection<? extends Procedure>)newValue);
				return;
			case DfPackage.ACTOR__STATE_VARS:
				getStateVars().clear();
				getStateVars().addAll((Collection<? extends Var>)newValue);
				return;
			case DfPackage.ACTOR__NATIVE:
				setNative((Boolean)newValue);
				return;
		}
		super.eSet(featureID, newValue);
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected EClass eStaticClass() {
		return DfPackage.Literals.ACTOR;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public void eUnset(int featureID) {
		switch (featureID) {
			case DfPackage.ACTOR__ACTIONS:
				getActions().clear();
				return;
			case DfPackage.ACTOR__ACTIONS_OUTSIDE_FSM:
				getActionsOutsideFsm().clear();
				return;
			case DfPackage.ACTOR__FSM:
				setFsm((FSM)null);
				return;
			case DfPackage.ACTOR__INITIALIZES:
				getInitializes().clear();
				return;
			case DfPackage.ACTOR__INPUTS:
				getInputs().clear();
				return;
			case DfPackage.ACTOR__MO_C:
				setMoC((MoC)null);
				return;
			case DfPackage.ACTOR__OUTPUTS:
				getOutputs().clear();
				return;
			case DfPackage.ACTOR__PARAMETERS:
				getParameters().clear();
				return;
			case DfPackage.ACTOR__PROCS:
				getProcs().clear();
				return;
			case DfPackage.ACTOR__STATE_VARS:
				getStateVars().clear();
				return;
			case DfPackage.ACTOR__NATIVE:
				setNative(NATIVE_EDEFAULT);
				return;
		}
		super.eUnset(featureID);
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Action> getActions() {
		if (actions == null) {
			actions = new EObjectContainmentEList<Action>(Action.class, this, DfPackage.ACTOR__ACTIONS);
		}
		return actions;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Action> getActionsOutsideFsm() {
		if (actionsOutsideFsm == null) {
			actionsOutsideFsm = new EObjectResolvingEList<Action>(Action.class, this, DfPackage.ACTOR__ACTIONS_OUTSIDE_FSM);
		}
		return actionsOutsideFsm;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public FSM getFsm() {
		return fsm;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Action> getInitializes() {
		if (initializes == null) {
			initializes = new EObjectContainmentEList<Action>(Action.class, this, DfPackage.ACTOR__INITIALIZES);
		}
		return initializes;
	}

	@Override
	public Port getInput(String name) {
		for (Port port : getInputs()) {
			if (port.getName().equals(name)) {
				return port;
			}
		}
		return null;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Port> getInputs() {
		if (inputs == null) {
			inputs = new EObjectContainmentEList<Port>(Port.class, this, DfPackage.ACTOR__INPUTS);
		}
		return inputs;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public MoC getMoC() {
		return moC;
	}

	@Override
	public Port getOutput(String name) {
		for (Port port : getOutputs()) {
			if (port.getName().equals(name)) {
				return port;
			}
		}
		return null;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Port> getOutputs() {
		if (outputs == null) {
			outputs = new EObjectContainmentEList<Port>(Port.class, this, DfPackage.ACTOR__OUTPUTS);
		}
		return outputs;
	}

	@Override
	public Var getParameter(String name) {
		for (Var var : getParameters()) {
			if (var.getName().equals(name)) {
				return var;
			}
		}
		return null;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Var> getParameters() {
		if (parameters == null) {
			parameters = new EObjectContainmentEList<Var>(Var.class, this, DfPackage.ACTOR__PARAMETERS);
		}
		return parameters;
	}

	@Override
	public Port getPort(String name) {
		Port port = getInput(name);
		if (port != null) {
			return port;
		}

		return getOutput(name);
	}

	@Override
	public Procedure getProcedure(String name) {
		return mapProcedures.get(name);
	}

	public Map<String, Procedure> getProceduresMap() {
		return mapProcedures;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Procedure> getProcs() {
		if (procs == null) {
			procs = new EObjectContainmentEList<Procedure>(Procedure.class, this, DfPackage.ACTOR__PROCS);
		}
		return procs;
	}

	@Override
	public Var getStateVar(String name) {
		return mapStateVars.get(name);
	}

	public Map<String, Var> getStateVariablesMap() {
		return mapStateVars;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public EList<Var> getStateVars() {
		if (stateVars == null) {
			stateVars = new EObjectContainmentEList<Var>(Var.class, this, DfPackage.ACTOR__STATE_VARS);
		}
		return stateVars;
	}

	@Override
	public boolean hasFsm() {
		return fsm != null;
	}

	@Override
	public boolean hasMoC() {
		return moC != null;
	}

	@Override
	public boolean isActor() {
		return true;
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public boolean isNative() {
		return native_;
	}

	@Override
	public void resetTokenConsumption() {
		for (Port port : inputs) {
			port.resetTokenConsumption();
		}
	}

	@Override
	public void resetTokenProduction() {
		for (Port port : outputs) {
			port.resetTokenProduction();
		}
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public void setFsm(FSM newFsm) {
		if (newFsm != fsm) {
			NotificationChain msgs = null;
			if (fsm != null)
				msgs = ((InternalEObject)fsm).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DfPackage.ACTOR__FSM, null, msgs);
			if (newFsm != null)
				msgs = ((InternalEObject)newFsm).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DfPackage.ACTOR__FSM, null, msgs);
			msgs = basicSetFsm(newFsm, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, DfPackage.ACTOR__FSM, newFsm, newFsm));
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public void setMoC(MoC newMoC) {
		if (newMoC != moC) {
			NotificationChain msgs = null;
			if (moC != null)
				msgs = ((InternalEObject)moC).eInverseRemove(this, EOPPOSITE_FEATURE_BASE - DfPackage.ACTOR__MO_C, null, msgs);
			if (newMoC != null)
				msgs = ((InternalEObject)newMoC).eInverseAdd(this, EOPPOSITE_FEATURE_BASE - DfPackage.ACTOR__MO_C, null, msgs);
			msgs = basicSetMoC(newMoC, msgs);
			if (msgs != null) msgs.dispatch();
		}
		else if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, DfPackage.ACTOR__MO_C, newMoC, newMoC));
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	public void setNative(boolean newNative) {
		boolean oldNative = native_;
		native_ = newNative;
		if (eNotificationRequired())
			eNotify(new ENotificationImpl(this, Notification.SET, DfPackage.ACTOR__NATIVE, oldNative, native_));
	}

	/**
	 * <!-- begin-user-doc --> <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	public String toString() {
		if (eIsProxy()) return super.toString();

		StringBuffer result = new StringBuffer(super.toString());
		result.append(" (native: ");
		result.append(native_);
		result.append(')');
		return result.toString();
	}

} // ActorImpl