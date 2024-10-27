from QuizCreationManager import QuizCreationManager
from QuizRetrievalManager import QuizRetrievalManager
from QuizSubmissionManager import QuizSubmissionManager

"""
The QuizManager class acts as a controller, delegating quiz-related tasks such as creation, retrieval, and submission to the respective manager classes.
@requires A valid DatabaseManager, session, and managers for quiz creation, retrieval, and submission
@ensures Centralized management of quiz-related operations by coordinating between different managers
"""
class QuizManager:
    """
    Initialize the QuizManager and set up all the quiz-related managers
    db_manager: DatabaseManager - The manager responsible for database operations
    session: dict - The session object for tracking user information
    @requires A valid DatabaseManager and session object
    @ensures QuizManager is ready to handle quiz creation, retrieval, and submission
    """
    def __init__(self, db_manager, session):
        self.quiz_creation = QuizCreationManager(db_manager)
        self.quiz_retrieval = QuizRetrievalManager(db_manager)
        self.quiz_submission = QuizSubmissionManager(db_manager, self.quiz_retrieval)

    """
    Delegate the quiz creation process to QuizCreationManager
    @requires QuizCreationManager to be initialized
    @ensures Quiz creation is handled by QuizCreationManager
    """
    def create_quiz(self):
        return self.quiz_creation.create_quiz()

    """
    Delegate the quiz submission process to QuizCreationManager
    @requires QuizCreationManager to be initialized
    @ensures Quiz submission is handled by QuizCreationManager
    """
    def submit_quiz(self):
        return self.quiz_creation.submit_quiz()

    """
    Fetch the quizzes created by a user
    user_email: str - The email of the user
    @requires A valid user_email and QuizRetrievalManager to be initialized
    @ensures Returns the quizzes created by the user
    """
    def get_user_quizzes(self, user_email):
        return self.quiz_retrieval.get_user_quizzes(user_email)

    """
    Delegate fetching the quiz details to QuizRetrievalManager
    quiz_id: int - The ID of the quiz
    @requires QuizRetrievalManager to be initialized
    @ensures Quiz details are fetched and rendered
    """
    def quiz_detail(self, quiz_id):
        return self.quiz_retrieval.quiz_detail(quiz_id)

    """
    Delegate the process of taking a quiz to QuizSubmissionManager
    quiz_id: int - The ID of the quiz
    question_num: int - The current question number
    @requires QuizSubmissionManager to be initialized
    @ensures The quiz is rendered with the current question
    """
    def take_quiz(self, quiz_id, question_num):
        return self.quiz_submission.take_quiz(quiz_id, question_num)

    """
    Delegate submitting an answer to a quiz question to QuizSubmissionManager
    quiz_id: int - The ID of the quiz
    question_num: int - The current question number
    @requires QuizSubmissionManager to be initialized
    @ensures The answer is submitted and the next question is rendered or the score is shown
    """
    def submit_quiz_answer(self, quiz_id, question_num):
        return self.quiz_submission.submit_quiz_answer(quiz_id, question_num)

    """
    Display the final quiz score to the user
    quiz_id: int - The ID of the quiz
    score: int - The user's score
    total: int - The total number of questions
    @requires Valid quiz_id, score, and total
    @ensures The final quiz score is rendered
    """
    def score(self, quiz_id, score, total):
        return self.quiz_submission.score(quiz_id, score, total)

    """
    Display the penalty for an incorrect quiz answer
    quiz_id: int - The ID of the quiz
    question_num: int - The current question number
    @requires QuizSubmissionManager to be initialized
    @ensures The penalty screen is shown for incorrect answers
    """
    def penalty(self, quiz_id, question_num):
        return self.quiz_submission.penalty(quiz_id, question_num)
