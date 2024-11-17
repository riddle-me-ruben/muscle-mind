from flask import session, request, redirect, url_for, render_template

"""
The QuizSubmissionManager class handles user interactions with quizzes, including submitting answers, tracking scores, and managing penalties.
@requires A valid DatabaseManager for storing and retrieving quiz data, and a QuizRetrievalManager for fetching quiz questions
@ensures Quizzes are properly submitted, scored, and penalties are handled for incorrect answers
"""
class QuizSubmissionManager:
    """
    Initialize the QuizSubmissionManager with a database and retrieval manager
    db_manager: DatabaseManager - The manager responsible for database operations
    retrieval_manager: QuizRetrievalManager - The manager responsible for quiz fetching
    @requires A valid DatabaseManager and QuizRetrievalManager instance
    @ensures QuizSubmissionManager is ready to handle quiz submissions and answer evaluations
    """
    def __init__(self, db_manager, retrieval_manager):
        self.db_manager = db_manager
        self.retrieval_manager = retrieval_manager

    """
    Render the quiz question page for the given quiz and question number
    quiz_id: int - The ID of the quiz
    question_num: int - The current question number
    @requires A valid quiz_id and question_num
    @ensures The current question for the quiz is rendered
    """
    def take_quiz(self, quiz_id, question_num):
        quiz = self.retrieval_manager.get_quiz_by_id(quiz_id)

        if quiz is None:
            return "Quiz not found", 404

        if question_num >= len(quiz['questions']):
            return redirect(url_for('home'))
        return render_template('take-quiz.html', quiz=quiz, question_num=question_num, quiz_id=quiz_id)

    """
    Process the answer submitted by the user for the given question
    quiz_id: int - The ID of the quiz
    question_num: int - The current question number
    @requires A valid quiz_id, question_num, and answer submitted by the user
    @ensures The answer is checked and the next question or score is displayed
    """
    def submit_quiz_answer(self, quiz_id, question_num):
        quiz = self.retrieval_manager.get_quiz_by_id(quiz_id)

        if quiz is None:
            return "Quiz not found", 404

        user_answer = request.form.get('answer')
        correct_answer = quiz['questions'][question_num]['correct_option']
        current_score = session.get('current_score', 0)

        if user_answer == correct_answer:
            session['current_score'] = current_score + 1
            if question_num + 1 < len(quiz['questions']):
                return redirect(url_for('take_quiz_route', quiz_id=quiz_id, question_num=question_num + 1))
            else:
                # Increment play count after the last question is answered
                user_email = session.get('email')
                if user_email == quiz['creator_email']:
                    update_query = "UPDATE quizzes SET creator_play_count = creator_play_count + 1 WHERE quiz_id = %s"
                else:
                    update_query = "UPDATE quizzes SET user_play_count = user_play_count + 1 WHERE quiz_id = %s"

                # Update the play count in the database
                self.db_manager.execute_commit(update_query, (quiz_id,))
                return redirect(url_for('score_route', quiz_id=quiz_id, score=session['current_score'], total=len(quiz['questions'])))
        else:
            return redirect(url_for('penalty_route', quiz_id=quiz_id, question_num=question_num))

    """
    Render the score page after the quiz is completed
    quiz_id: int - The ID of the quiz
    score: int - The score achieved by the user
    total: int - The total number of questions
    @requires A valid quiz_id, score, and total
    @ensures The score page is rendered showing the final result
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
        
        # session.pop('current_score', None)
        return render_template('score.html', score=score, total=total)

    """
    Render the penalty page for an incorrect answer
    quiz_id: int - The ID of the quiz
    question_num: int - The current question number
    @requires A valid quiz_id and question_num
    @ensures The penalty page is rendered showing the incorrect answer
    """
    def penalty(self, quiz_id, question_num):
        quiz = self.retrieval_manager.get_quiz_by_id(quiz_id)
        if quiz is None:
            return "Quiz not found", 404
        return render_template('penalty.html', quiz_id=quiz_id, question_num=question_num, total_questions=len(quiz['questions']), score=session.get('current_score', 0))
