from QuizCreationManager import QuizCreationManager
from QuizRetrievalManager import QuizRetrievalManager
from QuizSubmissionManager import QuizSubmissionManager
from flask import redirect, url_for, flash, session

"""
Description:
The QuizManager class serves as a centralized controller for managing quiz-related tasks. It delegates specific 
operations such as creation, retrieval, and submission to the respective manager classes. This ensures modularity 
and separation of concerns in the quiz management process.

Semi-formal Notation:
/*@ requires A valid DatabaseManager instance (db_manager != null) &&
  @ session is initialized and active &&
  @ QuizCreationManager, QuizRetrievalManager, and QuizSubmissionManager are properly instantiated;
  @ ensures QuizManager coordinates and delegates quiz-related tasks between managers:
  @   - Quiz creation via QuizCreationManager;
  @   - Quiz retrieval via QuizRetrievalManager;
  @   - Quiz submission via QuizSubmissionManager;
@*/
"""
class QuizManager:

    """
    Description:
    Initializes the QuizManager by creating instances of QuizCreationManager, QuizRetrievalManager, and 
    QuizSubmissionManager. This prepares the class to handle quiz-related tasks.

    Semi-formal Notation:
    /*@ requires db_manager != null (valid instance of DatabaseManager) &&
    @ session is active;
    @ ensures self.quiz_creation, self.quiz_retrieval, self.quiz_submission are instantiated and ready for use;
    @*/
    """
    def __init__(self, db_manager):
        self.quiz_creation = QuizCreationManager(db_manager)
        self.quiz_retrieval = QuizRetrievalManager(db_manager, None)
        self.quiz_submission = QuizSubmissionManager(db_manager, self.quiz_retrieval)


    """
    Description:
    Delegates the process of quiz creation to the QuizCreationManager. This method ensures that quiz creation 
    tasks, such as rendering forms and storing quizzes, are handled appropriately.

    Semi-formal Notation:
    /*@ requires self.quiz_creation != null (QuizCreationManager is instantiated);
    @ ensures Quiz creation process is delegated to self.quiz_creation.create_quiz();
    @*/
    """
    def create_quiz(self):
        return self.quiz_creation.create_quiz()

    """
    Description:
    Handles the deletion of a quiz by ID. Ensures that only logged-in users can delete quizzes and delegates the 
    deletion task to QuizRetrievalManager.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 (valid quiz ID) &&
    @ session['email'] != null (user is logged in);
    @ ensures Quiz with ID quiz_id is deleted if it belongs to the user identified by session['email'];
    @ ensures Redirects the user to the home page after deletion;
    @*/
    """
    def delete_quiz(self, quiz_id):
        if 'email' not in session:
            return redirect(url_for('login'))
        
        user_email = session['email']

        self.quiz_retrieval.delete_quiz(quiz_id, user_email)
        return redirect(url_for('home'))


    """
    Description:
    Delegates the quiz submission process to QuizCreationManager. Handles tasks such as validating and storing 
    submitted quiz data.

    Semi-formal Notation:
    /*@ requires self.quiz_creation != null (QuizCreationManager is instantiated);
    @ ensures Quiz submission process is delegated to self.quiz_creation.submit_quiz();
    @*/
    """
    def submit_quiz(self):
        return self.quiz_creation.submit_quiz()

    """
    Description:
    Fetches all quizzes created by a specific user. Delegates the retrieval task to QuizRetrievalManager.

    Semi-formal Notation:
    /*@ requires user_email is a valid string &&
    @ self.quiz_retrieval != null (QuizRetrievalManager is instantiated);
    @ ensures \result == self.quiz_retrieval.get_user_quizzes(user_email);
    @*/
    """
    def get_user_quizzes(self, user_email):
        return self.quiz_retrieval.get_user_quizzes(user_email)

    """
    Description:
    Fetches the details of a specific quiz identified by its ID. Delegates this task to QuizRetrievalManager.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 (valid quiz ID) &&
    @ self.quiz_retrieval != null (QuizRetrievalManager is instantiated);
    @ ensures \result == self.quiz_retrieval.quiz_detail(quiz_id);
    @*/
    """
    def quiz_detail(self, quiz_id):
        return self.quiz_retrieval.quiz_detail(quiz_id)

    """
    Description:
    Handles the process of taking a quiz by delegating to QuizSubmissionManager. Renders the quiz and the current 
    question.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 &&
    @ question_num >= 0 &&
    @ self.quiz_submission != null (QuizSubmissionManager is instantiated);
    @ ensures \result == self.quiz_submission.take_quiz(quiz_id, question_num);
    @*/
    """
    def take_quiz(self, quiz_id, question_num):
        return self.quiz_submission.take_quiz(quiz_id, question_num)

    """
    Description:
    Handles the submission of an answer for a specific quiz question. Delegates this task to QuizSubmissionManager.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 &&
    @ question_num >= 0 &&
    @ self.quiz_submission != null (QuizSubmissionManager is instantiated);
    @ ensures Answer for question_num in quiz_id is submitted and further actions are taken:
    @   - Render next question if available;
    @   - Render score if all questions are completed;
    @*/
    """
    def submit_quiz_answer(self, quiz_id, question_num):
        return self.quiz_submission.submit_quiz_answer(quiz_id, question_num)

    """
    Description:
    Displays the final score for a completed quiz. Delegates this task to QuizSubmissionManager.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 &&
    @ score >= 0 &&
    @ total > 0 &&
    @ self.quiz_submission != null (QuizSubmissionManager is instantiated);
    @ ensures \result == self.quiz_submission.score(quiz_id, score, total);
    @*/
    """
    def score(self, quiz_id, score, total):
        return self.quiz_submission.score(quiz_id, score, total)

    """
    Description:
    Displays the penalty screen for an incorrect answer. Delegates this task to QuizSubmissionManager.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 &&
    @ question_num >= 0 &&
    @ self.quiz_submission != null (QuizSubmissionManager is instantiated);
    @ ensures \result == self.quiz_submission.penalty(quiz_id, question_num);
    @*/
    """
    def penalty(self, quiz_id, question_num):
        return self.quiz_submission.penalty(quiz_id, question_num)