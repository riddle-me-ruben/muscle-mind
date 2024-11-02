from flask import render_template

"""
The QuizRetrievalManager class handles retrieving quizzes and their details from the database.
@requires A valid DatabaseManager for fetching quiz data
@ensures Quiz information is retrieved and processed for display, ensuring accurate data retrieval from the database
"""
class QuizRetrievalManager:
    """
    Initialize the QuizRetrievalManager with a database manager
    db_manager: DatabaseManager - The manager responsible for database operations
    @requires A valid DatabaseManager instance
    @ensures QuizRetrievalManager is ready to handle quiz fetching and detail retrieval
    """
    def __init__(self, db_manager):
        self.db_manager = db_manager


    def delete_quiz(self, quiz_id, user_email):
        """Delete a quiz by its ID and user email."""
        delete_query = "DELETE FROM quizzes WHERE quiz_id = %s AND user_email = %s"
        self.db_manager.execute_commit(delete_query, (quiz_id, user_email))

    """
    Fetch the quiz by its ID and construct the quiz data
    quiz_id: int - The ID of the quiz
    @requires A valid quiz_id and database connection
    @ensures The quiz data is returned including its questions and title
    """
    def get_quiz_by_id(self, quiz_id):
        quiz = self.fetch_quiz(quiz_id)
        if not quiz:
            return None
        questions = self.build_questions(quiz)
        return {'title': quiz[0][0], 'questions': questions}

    """
    Retrieve quiz details from the database by its ID
    quiz_id: int - The ID of the quiz
    @requires A valid quiz_id and database connection
    @ensures The quiz is fetched from the database
    """
    
    def fetch_quiz(self, quiz_id):
        quiz_query, params = self.build_quiz_query(quiz_id)
        quiz = self.db_manager.execute_query(quiz_query, params)
        return quiz

    """
    Build the SQL query to retrieve quiz details and questions
    quiz_id: int - The ID of the quiz
    @requires A valid quiz_id
    @ensures A dynamic SQL query is built to fetch the quiz data
    """
    def build_quiz_query(self, quiz_id):
        columns = ['title']
        num_questions = 10

        for i in range(num_questions):
            question_idx = i + 1
            columns += [
                f'question{question_idx}', f'option{question_idx}_1', f'option{question_idx}_2',
                f'option{question_idx}_3', f'option{question_idx}_4', f'correct_option{question_idx}'
            ]

        query = f"SELECT {', '.join(columns)} FROM quizzes WHERE quiz_id = %s"
        return query, (quiz_id,)

    """
    Build a list of questions from the fetched quiz result
    quiz: tuple - The quiz data fetched from the database
    @requires Valid quiz data containing questions and options
    @ensures A list of questions with their options and correct answers is built
    """
    def build_questions(self, quiz):
        """Build the list of questions from the quiz result."""
        num_questions = 10
        questions = []

        for i in range(num_questions):
            question_idx = 1 + i * 6  # Calculate the starting index for each question block
            if quiz[0][question_idx]:
                questions.append({
                    'question': quiz[0][question_idx],
                    'options': [
                        quiz[0][question_idx + 1],
                        quiz[0][question_idx + 2],
                        quiz[0][question_idx + 3],
                        quiz[0][question_idx + 4]
                    ],
                    'correct_option': quiz[0][question_idx + 5]
                })

        return questions

    """
    Render the quiz details page with the quiz data
    quiz_id: int - The ID of the quiz
    @requires A valid quiz_id and QuizRetrievalManager to be initialized
    @ensures The quiz detail page is rendered
    """
    def quiz_detail(self, quiz_id):
        """Render the quiz detail page."""
        quiz = self.get_quiz_by_id(quiz_id)
        if not quiz:
            return "Quiz not found", 404
        return render_template('quiz-detail.html', quiz=quiz)

    """
    Retrieve the list of quizzes created by a user
    user_email: str - The email of the user
    @requires A valid user_email and database connection
    @ensures The quizzes created by the user are returned
    """
    def get_user_quizzes(self, user_email):
        """Retrieve the quizzes created by the user and return them as a list of dictionaries."""
        query = "SELECT quiz_id, title FROM quizzes WHERE user_email = %s"
        result = self.db_manager.execute_query(query, (user_email,))
        
        # Convert result to a list of dictionaries
        quizzes = [{'quiz_id': row[0], 'title': row[1]} for row in result]
        return quizzes