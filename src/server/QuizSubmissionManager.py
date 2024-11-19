from flask import session, request, redirect, url_for, render_template

"""
Description:
The QuizSubmissionManager class manages user interactions with quizzes, including navigating through questions, 
submitting answers, updating scores, and handling penalties for incorrect responses. It integrates with the 
DatabaseManager for data storage and QuizRetrievalManager for fetching quiz details.

Semi-formal Notation:
/*@ requires db_manager != null (valid DatabaseManager instance) &&
  @ retrieval_manager != null (valid QuizRetrievalManager instance);
  @ ensures QuizSubmissionManager facilitates:
  @   - Navigating quiz questions via take_quiz;
  @   - Submitting and validating answers via submit_quiz_answer;
  @   - Rendering scores and penalties via score and penalty methods;
@*/
"""
class QuizSubmissionManager:

    """
    Description:
    Initializes the QuizSubmissionManager with a DatabaseManager for handling database operations and a 
    QuizRetrievalManager for accessing quiz details.

    Semi-formal Notation:
    /*@ requires db_manager != null (valid DatabaseManager instance) &&
    @ retrieval_manager != null (valid QuizRetrievalManager instance);
    @ ensures self.db_manager == db_manager &&
    @ ensures self.retrieval_manager == retrieval_manager;
    @*/
    """
    def __init__(self, db_manager, retrieval_manager):
        self.db_manager = db_manager
        self.retrieval_manager = retrieval_manager

    """
    Description:
    Renders the quiz question page for the given quiz and question number. Validates the quiz ID and ensures the 
    user is not navigating beyond the total number of questions.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 (valid quiz ID) &&
    @ question_num >= 0;
    @ ensures If quiz exists:
    @   Renders 'take-quiz.html' with quiz details and the current question;
    @ ensures If quiz does not exist:
    @   \result == ("Quiz not found", 404);
    @ ensures If question_num >= len(quiz['questions']):
    @   Redirects to home;
    @*/
    """
    def take_quiz(self, quiz_id, question_num):
        quiz = self.retrieval_manager.get_quiz_by_id(quiz_id)

        if quiz is None:
            return "Quiz not found", 404

        if question_num >= len(quiz['questions']):
            return redirect(url_for('home'))
        return render_template('take-quiz.html', quiz=quiz, question_num=question_num, quiz_id=quiz_id)

    """
    Description:
    Processes the user's answer for the current question, validates it against the correct answer, and navigates 
    to the next question or the score page. Updates the play count in the database upon completion.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 (valid quiz ID) &&
    @ question_num >= 0 &&
    @ request.form['answer'] contains the user's submitted answer;
    @ ensures If answer is correct:
    @   session['current_score'] is incremented &&
    @   Redirects to the next question if question_num + 1 < len(quiz['questions']);
    @ ensures If all questions are answered:
    @   Updates the play count for creator or user &&
    @   Redirects to score page with final score;
    @ ensures If answer is incorrect:
    @   Redirects to penalty page for the current question;
    @*/
    """
    def submit_quiz_answer(self, quiz_id, question_num):
        quiz = self.retrieval_manager.get_quiz_by_id(quiz_id)

        if quiz is None:
            return "Quiz not found", 404

        user_answer, correct_answer, current_score = request.form.get('answer'), quiz['questions'][question_num]['correct_option'], session.get('current_score', 0)

        # Increment play count regardless of the correctness of the last question
        if question_num + 1 == len(quiz['questions']):
            user_email = session.get('email')
            creator_email = quiz['creator_email']
            self.increment_play_count(user_email, creator_email, quiz_id)

        if user_answer != correct_answer:
            return redirect(url_for('penalty_route', quiz_id=quiz_id, question_num=question_num))

        session['current_score'] = current_score + 1

        if question_num + 1 < len(quiz['questions']):
            return redirect(url_for('take_quiz_route', quiz_id=quiz_id, question_num=question_num + 1))

        return redirect(url_for('score_route', quiz_id=quiz_id, score=session['current_score'], total=len(quiz['questions'])))

    """
    Description:
    Increments the play count for a quiz. If the user is the creator, increments the creator's play count; 
    otherwise, increments the user's play count.

    Semi-formal Notation:
    /*@ requires user_email and creator_email are valid non-null strings &&
    @ quiz_id > 0 (valid quiz ID);
    @ ensures If user_email == creator_email:
    @   Updates creator_play_count in the database;
    @ ensures If user_email != creator_email:
    @   Updates user_play_count in the database;
    @*/
    """
    def increment_play_count(self, user_email, creator_email, quiz_id):
        if user_email == creator_email:
            update_query = "UPDATE quizzes SET creator_play_count = creator_play_count + 1 WHERE quiz_id = %s"
        else:
            update_query = "UPDATE quizzes SET user_play_count = user_play_count + 1 WHERE quiz_id = %s"
        
        # Update the play count in the database
        self.db_manager.execute_commit(update_query, (quiz_id,))

    """
    Description:
    Renders the score page showing the user's performance after completing the quiz. Updates user statistics in the 
    database, including total questions answered and score.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 (valid quiz ID) &&
    @ score >= 0 &&
    @ total > 0;
    @ ensures If user_email exists in session:
    @   Updates or inserts user statistics in the `user_quiz_stats` table;
    @ ensures session['current_score'] is cleared &&
    @ ensures Renders 'score.html' with final score and total questions;
    @*/
    """
    def score(self, quiz_id, score, total):
        user_email = session.get('email')
        if user_email:
            query = """
                INSERT INTO user_quiz_stats (user_email, quiz_id, questions_answered, score)
                VALUES (%s, %s, %s, %s)
                ON DUPLICATE KEY UPDATE
                questions_answered = questions_answered + %s,
                score = score + %s
            """
            self.db_manager.execute_commit(query, (user_email, quiz_id, total, score, total, score))
        
        session.pop('current_score', None)
        return render_template('score.html', score=score, total=total)

    """
    Description:
    Renders the penalty page when the user submits an incorrect answer. Displays the current score and the total 
    number of questions in the quiz.

    Semi-formal Notation:
    /*@ requires quiz_id > 0 (valid quiz ID) &&
    @ question_num >= 0;
    @ ensures If quiz exists:
    @   Renders 'penalty.html' with quiz_id, question_num, total_questions, and current score;
    @ ensures If quiz does not exist:
    @   \result == ("Quiz not found", 404);
    @*/
    """
    def penalty(self, quiz_id, question_num):
        quiz = self.retrieval_manager.get_quiz_by_id(quiz_id)
        if quiz is None:
            return "Quiz not found", 404
        return render_template('penalty.html', quiz_id=quiz_id, question_num=question_num, total_questions=len(quiz['questions']), score=session.get('current_score', 0))