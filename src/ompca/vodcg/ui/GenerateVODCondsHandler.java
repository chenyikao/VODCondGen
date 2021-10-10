package ompca.vodcg.ui;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;

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

import ompca.vodcg.ASTUtil;
import ompca.vodcg.VODCondGen;
import ompca.vodcg.VariablePath;

public class GenerateVODCondsHandler extends AbstractHandler {

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
			IPath varFilePath 		= feInput.getPath();
			IProject project 		= fInput.getProject();

			ASTUtil.setSelectedProject(project);

			ResourceListSelectionDialog dialog = new ResourceListSelectionDialog(
					HandlerUtil.getActiveShell(event), project, IResource.FILE) {

				protected String adjustPattern() {
					String s = super.adjustPattern();
					if (s.equals("")) return "*.c";
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
			dialog.setTitle("Please specify where the main function is:");
			dialog.setInitialSelections(new Object[] {fInput});
			if (dialog.open() == Window.OK) {
				Object[] result = dialog.getResult();
				if (result != null && result.length == 1) {
//					System.getProperty("java.classpath");
					final IFile mainC = (IFile) result[0];
					final IPath mainPath = mainC.getLocation();
					final String outPath = mainPath.removeLastSegments(1).append("conditions").append(mainC.getName()).toOSString() + ".smt2", 
							task = "Generating " + outPath;
					final VODCondGen condGen = VODCondGen.from(mainPath, Display.getCurrent());
					
					final Job job = new Job(task) {
						protected IStatus run(IProgressMonitor monitor) {
							condGen.setStart(monitor, task, VariablePath.from(ts, varFilePath, condGen));
							try {
								PrintStream outFile = new PrintStream(new File(outPath));
								outFile.print(condGen.generateConditionString());
								outFile.close();
								
							} catch (FileNotFoundException e) {	// top level general debugging?
								e.printStackTrace();
								return Status.CANCEL_STATUS;
//								DebugElement.throwTodoException(e);
							}
							condGen.done(null, "Condition generated!");
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