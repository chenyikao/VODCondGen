package ompca.vodcg.ui;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.dialogs.ResourceListSelectionDialog;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.part.FileEditorInput;

import ompca.solver.Solver;
import ompca.vodcg.ASTUtil;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.VariablePath;

public class SolveVODCondsHandler extends AbstractHandler {

	public Object execute(ExecutionEvent event)
			throws ExecutionException {
		Display display = Display.getCurrent();
		if (display == null) display = Display.getDefault();
		if (display != null) display.beep();		

		// selection type is already filtered in the extension expression
		ITextSelection ts = (ITextSelection) HandlerUtil.getCurrentSelection(event);
		if (ts != null && !ts.isEmpty()) {
			IWorkbenchWindow win = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
			assert(win != null);
			IWorkbenchPage page = win.getActivePage();
			assert(page != null);
			IEditorPart editor = page.getActiveEditor();
			assert(editor != null);
			IEditorInput input = editor.getEditorInput();
			assert(input != null);
			FileEditorInput feInput = (FileEditorInput)input;
			IFile fInput 			= feInput.getFile();
			IPath varPath 			= feInput.getPath(), mainPath = null;
			IProject project 		= fInput.getProject();

			ASTUtil.setSelectedProject(project);

			ResourceListSelectionDialog dialog = new ResourceListSelectionDialog(
					HandlerUtil.getActiveShell(event), project, IResource.FILE) {

				protected String adjustPattern() {
					String s = super.adjustPattern();
					if (s.equals("")) return "*.smt2";
					return s;
				}

				public void create() {
					super.create();
					refresh(true);
				}
				
//				protected boolean select(IResource resource) {
//					if (!(resource instanceof IFile)) {updateOKState(false); return false;}
//					return super.select(resource);
//				}

//				protected void updateOKState(boolean state) {
//					super.updateOKState(true); // allow to select nothing
//				}
			};
			dialog.setTitle("Please specify the SMT2 file to solve:");
			dialog.setInitialSelections(new Object[] {fInput});
			if (dialog.open() == Window.OK) {
				Object[] result = dialog.getResult();
				if (result != null && result.length == 1) {
//					System.getProperty("java.classpath");
					mainPath = ((IFile)result[0]).getLocation();
					final String osPath = mainPath.toOSString(), outPath = osPath + ".txt", task = "Solving to " + outPath;
					final VODCondGen condGen = VODCondGen.from(mainPath, Display.getCurrent());
					
					final Job job = new Job(task) {
						protected IStatus run(IProgressMonitor monitor) {
							condGen.setStart(monitor, task, VariablePath.from(ts, varPath, condGen));
							Solver.main(new String[] {osPath, "-rd:In"});
//							try {
//								PrintStream outFile = new PrintStream(new File(outPath));
//								outFile.print();
//								outFile.close();
//								
//							} catch (FileNotFoundException e) {	// top level general debugging?
//								DebugElement.throwTodoException(e);
//								return Status.CANCEL_STATUS;
//							}
							condGen.done(null, "Condition solving ends!");
							return Status.OK_STATUS;
						}
					};
					job.schedule();
				}					
			}
		}
		return null;
	}

}